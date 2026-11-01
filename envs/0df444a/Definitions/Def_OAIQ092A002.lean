-- Prove2me | Definitions.Def_OAIQ092A002
-- name    : OAIQ092A002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T19:46:42.410625+00:00
-- url     : https://prove2.me/theorems/98ae4c64-f863-46c1-af8c-5f4cb49d0d00
-- title:
--   Definitions bundle OAIQ092A002 of the split of OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 921 declarations of OpenAI's Lean: 600 definitions, 6 inductive types or structures, 1 instance and 314 theorems. The definitions and types are `OAI.ContinuumCoulomb.QMAReferenceTerm`, `OAI.ContinuumCoulomb.QMASortedPorts`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.routeLengthBound`, `OAI.ContinuumCoulomb.QMATransferDisjoint`, `OAI.ContinuumCoulomb.QMAXZField`, `OAI.ContinuumCoulomb.QMAXZFieldIndex`, `OAI.ContinuumCoulomb.QMAXZModel`, `OAI.ContinuumCoulomb.QMAXZPair`, `OAI.ContinuumCoulomb.QMAXZPairIndex`, `OAI.ContinuumCoulomb.QMAXZScalarIndex`, `OAI.ContinuumCoulomb.QMAXZTerm`, `OAI.ContinuumCoulomb.QMAXZTerm.IsField`, `OAI.ContinuumCoulomb.QMAXZTerm.IsPair`, `OAI.ContinuumCoulomb.QMAXZTerm.IsScalar`, `OAI.ContinuumCoulomb.QMAXZTerm.asField`, `OAI.ContinuumCoulomb.QMAXZTerm.asPair`, `OAI.ContinuumCoulomb.QMAXZTerm.matrix`, `OAI.ContinuumCoulomb.QMAXZTerm.word`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.adjoint`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.denote`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.diagonal`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.hadamard`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.identity`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.matMul`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.oneReference`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.phaseT`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.referenceState`, `OAI.ContinuumCoulomb.QuantumAlgebraicHistory.reindex`, `OAI.ContinuumCoulomb.QuantumAlgebraicScalar.RealScalar`, `OAI.ContinuumCoulomb.QuantumAlgebraicScalar.Scalar`, `OAI.ContinuumCoulomb.QuantumAlgebraicScalar.add`, `OAI.ContinuumCoulomb.QuantumAlgebraicScalar.conj`, `OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height`, `OAI.ContinuumCoulomb.QuantumAlgebraicScalar.imagPart`, `OAI.ContinuumCoulomb.QuantumAlgebraicScalar.imaginary`, `OAI.ContinuumCoulomb.QuantumAlgebraicScalar.mul`, `OAI.ContinuumCoulomb.QuantumAlgebraicScalar.neg`, `OAI.ContinuumCoulomb.QuantumAlgebraicScalar.product`, `OAI.ContinuumCoulomb.QuantumAlgebraicScalar.rat`, `OAI.ContinuumCoulomb.QuantumAlgebraicScalar.realAdd` and 566 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/Computability, lean/OAI/MathematicalPhysics, in whole or in part: `Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateL2`, `ContinuumCoulomb_ManyBody_ChargeTransfer`, `ContinuumCoulomb_ManyBody_FiniteCubeQuadrature`, `ContinuumCoulomb_ManyBody_GlobalSinglet`, `ContinuumCoulomb_ManyBody_MediatorCompression`, `ContinuumCoulomb_ManyBody_Singlet`, `ContinuumCoulomb_ManyBody_Spin`, `ContinuumCoulomb_Nuclei_FlowJetCoordinates`, `ContinuumCoulomb_Nuclei_SlabBoxSchedule`, `ContinuumCoulomb_Nuclei_SlabCoordinates`, `ContinuumCoulomb_Nuclei_SlabLineIntegral`, `ContinuumCoulomb_Nuclei_SlabOriginQuadrature`, `ContinuumCoulomb_Nuclei_TransportedFarQuadrature`, `ContinuumCoulomb_OneParticle_AtomicOutputs`, `ContinuumCoulomb_OneParticle_BoundedPotentialOperator`, `ContinuumCoulomb_OneParticle_CappedCoulombKernel`, `ContinuumCoulomb_OneParticle_CappedCoulombTruncation`, `ContinuumCoulomb_OneParticle_ClassicalTensor`, `ContinuumCoulomb_OneParticle_ContactAdjustment`, `ContinuumCoulomb_OneParticle_ContactGadgets`, `ContinuumCoulomb_OneParticle_ContactTemplates`, `ContinuumCoulomb_OneParticle_CubeGeometry`, `ContinuumCoulomb_OneParticle_CubeMeasure`, `ContinuumCoulomb_OneParticle_OrbitalCutoff`, `ContinuumCoulomb_OneParticle_RationalHeatPlaneError`, `ContinuumCoulomb_OneParticle_RectangleQuadrature`, `ContinuumCoulomb_OneParticle_UnitBinaryInclusion`, `ContinuumCoulomb_Programs_PolynomialTimeSize`, `ContinuumCoulomb_Programs_UnitBinaryProgram`, `ContinuumCoulomb_Quantum_ClockPathBound`, `ContinuumCoulomb_Quantum_QuantumAdjacentProgram`, `ContinuumCoulomb_Quantum_QuantumAlgebraicHeight`, `ContinuumCoulomb_Quantum_QuantumAlgebraicHistory`, `ContinuumCoulomb_Quantum_QuantumAlgebraicScalar`, `ContinuumCoulomb_Quantum_QuantumAxisSample`, `ContinuumCoulomb_Quantum_QuantumBitTransfer`, `ContinuumCoulomb_Quantum_QuantumBlockBudget`, `ContinuumCoulomb_Quantum_QuantumBlockEdges`, `ContinuumCoulomb_Quantum_QuantumBlockHamiltonian`, `ContinuumCoulomb_Quantum_QuantumBufferedArmProgram`, `ContinuumCoulomb_Quantum_QuantumBufferedArms`, `ContinuumCoulomb_Quantum_QuantumBufferedCells`, `ContinuumCoulomb_Quantum_QuantumBufferedDetour`, `ContinuumCoulomb_Quantum_QuantumBufferedDogleg`, `ContinuumCoulomb_Quantum_QuantumBufferedFanout`, `ContinuumCoulomb_Quantum_QuantumBufferedIntersections`, `ContinuumCoulomb_Quantum_QuantumBufferedLanes`, `ContinuumCoulomb_Quantum_QuantumBufferedPortRealization`, `ContinuumCoulomb_Quantum_QuantumCircuitCode`, `ContinuumCoulomb_Quantum_QuantumClockAnchor`, `ContinuumCoulomb_Quantum_QuantumClockTransition`, `ContinuumCoulomb_Quantum_QuantumCoefficientEnvelopeProgram`, `ContinuumCoulomb_Quantum_QuantumCoefficientPrograms`, `ContinuumCoulomb_Quantum_QuantumComputedRoutingTable`, `ContinuumCoulomb_Quantum_QuantumCorridorEndpoints`, `ContinuumCoulomb_Quantum_QuantumCorridorInterior`, `ContinuumCoulomb_Quantum_QuantumCountertermSample`, `ContinuumCoulomb_Quantum_QuantumCrossingBounds`, `ContinuumCoulomb_Quantum_QuantumCrossingCoefficientBound`, `ContinuumCoulomb_Quantum_QuantumCrossingEffective`, `ContinuumCoulomb_Quantum_QuantumCrossingListBlock`, `ContinuumCoulomb_Quantum_QuantumCrossingListFamily`, `ContinuumCoulomb_Quantum_QuantumCrossingScaleProgram`, `ContinuumCoulomb_Quantum_QuantumCrossingSelectCorrectness`, `ContinuumCoulomb_Quantum_QuantumCrossingsGraph`, `ContinuumCoulomb_Quantum_QuantumDiagonalTensor`, `ContinuumCoulomb_Quantum_QuantumEndpointListProgram`, `ContinuumCoulomb_Quantum_QuantumEndpointPorts`, `ContinuumCoulomb_Quantum_QuantumExchangeLanes`, `ContinuumCoulomb_Quantum_QuantumExchangeSample`, `ContinuumCoulomb_Quantum_QuantumExchangeSampleProgram`, `ContinuumCoulomb_Quantum_QuantumFinalRoutingProgram`, `ContinuumCoulomb_Quantum_QuantumFineRoute`, `ContinuumCoulomb_Quantum_QuantumFiniteMembership`, `ContinuumCoulomb_Quantum_QuantumFiniteRouteSearch`, `ContinuumCoulomb_Quantum_QuantumFirstUseProgram`, `ContinuumCoulomb_Quantum_QuantumFirstUseSites`, `ContinuumCoulomb_Quantum_QuantumFixedMatrixProgram`, `ContinuumCoulomb_Quantum_QuantumFixedPauli`, `ContinuumCoulomb_Quantum_QuantumFixedPauliProgram`, `ContinuumCoulomb_Quantum_QuantumForkCells`, `ContinuumCoulomb_Quantum_QuantumForkDegreeBound`, `ContinuumCoulomb_Quantum_QuantumForkDegrees`, `ContinuumCoulomb_Quantum_QuantumForkGraph`, `ContinuumCoulomb_Quantum_QuantumForkInitial`, `ContinuumCoulomb_Quantum_QuantumForkInitialCells`, `ContinuumCoulomb_Quantum_QuantumForkListBoundProgram`, `ContinuumCoulomb_Quantum_QuantumForkListCellMass`, `ContinuumCoulomb_Quantum_QuantumForkListData`, `ContinuumCoulomb_Quantum_QuantumForkListDegree`, `ContinuumCoulomb_Quantum_QuantumForkListEnvelope`, `ContinuumCoulomb_Quantum_QuantumForkListFullDegree`, `ContinuumCoulomb_Quantum_QuantumForkListGraph`, `ContinuumCoulomb_Quantum_QuantumForkListIndex`, `ContinuumCoulomb_Quantum_QuantumForkListInitialPairs`, `ContinuumCoulomb_Quantum_QuantumForkListInitialPhysical`, `ContinuumCoulomb_Quantum_QuantumForkListInitialSpatial`, `ContinuumCoulomb_Quantum_QuantumForkListIterateWeights`, `ContinuumCoulomb_Quantum_QuantumForkListNext`, `ContinuumCoulomb_Quantum_QuantumForkListNextPorts`, `ContinuumCoulomb_Quantum_QuantumForkListNextValid`, `ContinuumCoulomb_Quantum_QuantumForkListOrdinal`, `ContinuumCoulomb_Quantum_QuantumForkListOuter`, `ContinuumCoulomb_Quantum_QuantumForkListOutputBounds`, `ContinuumCoulomb_Quantum_QuantumForkListPartition`, `ContinuumCoulomb_Quantum_QuantumForkListPoints`, `ContinuumCoulomb_Quantum_QuantumForkListSites`, `ContinuumCoulomb_Quantum_QuantumForkListSize`, `ContinuumCoulomb_Quantum_QuantumForkListSum`, `ContinuumCoulomb_Quantum_QuantumFourAxis`, `ContinuumCoulomb_Quantum_QuantumFourSpatial`, `ContinuumCoulomb_Quantum_QuantumGateScalarReduction`, `ContinuumCoulomb_Quantum_QuantumGateUnitary`, `ContinuumCoulomb_Quantum_QuantumGeometryPowers`, `ContinuumCoulomb_Quantum_QuantumGridNeighbors`, `ContinuumCoulomb_Quantum_QuantumHistoryBitProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryCells`, `ContinuumCoulomb_Quantum_QuantumHistoryComparison`, `ContinuumCoulomb_Quantum_QuantumHistoryDegree`, `ContinuumCoulomb_Quantum_QuantumHistoryDescriptorProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryDescriptors`, `ContinuumCoulomb_Quantum_QuantumHistoryEnumeration`, `ContinuumCoulomb_Quantum_QuantumHistoryIncidence`, `ContinuumCoulomb_Quantum_QuantumHistoryLattice`, `ContinuumCoulomb_Quantum_QuantumHistoryParameterBounds`, `ContinuumCoulomb_Quantum_QuantumHistorySamplerProgram`, `ContinuumCoulomb_Quantum_QuantumHistorySizeBounds`, `ContinuumCoulomb_Quantum_QuantumHistorySpatial`, `ContinuumCoulomb_Quantum_QuantumInnerPorts`, `ContinuumCoulomb_Quantum_QuantumLaneSupport`, `ContinuumCoulomb_Quantum_QuantumLatticeCoefficient`, `ContinuumCoulomb_Quantum_QuantumLatticeEncoding`, `ContinuumCoulomb_Quantum_QuantumLatticeEnvelope`, `ContinuumCoulomb_Quantum_QuantumLatticeSerialization`, `ContinuumCoulomb_Quantum_QuantumLatticeSource`, `ContinuumCoulomb_Quantum_QuantumListMerge`, `ContinuumCoulomb_Quantum_QuantumListPathProgram`, `ContinuumCoulomb_Quantum_QuantumListRouteSelection`, `ContinuumCoulomb_Quantum_QuantumListScheduleGeometry`, `ContinuumCoulomb_Quantum_QuantumLocalAction`, `ContinuumCoulomb_Quantum_QuantumLocalCoordinates`, `ContinuumCoulomb_Quantum_QuantumLocalJoin`, `ContinuumCoulomb_Quantum_QuantumLocalPenalties`, `ContinuumCoulomb_Quantum_QuantumManhattanSupport`, `ContinuumCoulomb_Quantum_QuantumMergedSupport`, `ContinuumCoulomb_Quantum_QuantumOffsetSample`, `ContinuumCoulomb_Quantum_QuantumOrderedCoefficient`, `ContinuumCoulomb_Quantum_QuantumOrderedFinalBounds`, `ContinuumCoulomb_Quantum_QuantumOrderedIncidence`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelBlocks`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelCompile`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelCorrectness`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelData`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelFamily`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelOutput`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelPacking`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelPipeline`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelProgram`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelSubdivision`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelTable`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelThird`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelYY`, `ContinuumCoulomb_Quantum_QuantumOrderedOutputBounds`, `ContinuumCoulomb_Quantum_QuantumOrderedPrivate`, `ContinuumCoulomb_Quantum_QuantumOrderedRawBlock`, `ContinuumCoulomb_Quantum_QuantumOrderedRawPacking`, `ContinuumCoulomb_Quantum_QuantumOrderedRawPackingProgram`, `ContinuumCoulomb_Quantum_QuantumOrderedSourceIndex`, `ContinuumCoulomb_Quantum_QuantumOrderedSpatialComplete`, `ContinuumCoulomb_Quantum_QuantumOrderedSplit`, `ContinuumCoulomb_Quantum_QuantumOrderedSubdivision`, `ContinuumCoulomb_Quantum_QuantumOrderedThird`, `ContinuumCoulomb_Quantum_QuantumOrderedThirdSites`, `ContinuumCoulomb_Quantum_QuantumOrderedTriple`, `ContinuumCoulomb_Quantum_QuantumOrderedTripleFactors`, `ContinuumCoulomb_Quantum_QuantumOrderedTwoStage`, `ContinuumCoulomb_Quantum_QuantumOrderedWeightBounds`, `ContinuumCoulomb_Quantum_QuantumOrderedWeightProgram`, `ContinuumCoulomb_Quantum_QuantumOrderedXZPipeline`, `ContinuumCoulomb_Quantum_QuantumOrderedXZTerm`, `ContinuumCoulomb_Quantum_QuantumOrderedYYFactors`, `ContinuumCoulomb_Quantum_QuantumOrderedYYReduction`, `ContinuumCoulomb_Quantum_QuantumOrdinalProgram`, `ContinuumCoulomb_Quantum_QuantumOrdinalSlots`, `ContinuumCoulomb_Quantum_QuantumPaddedHistory`, `ContinuumCoulomb_Quantum_QuantumPaddedLabelData`, `ContinuumCoulomb_Quantum_QuantumPaddedLabelMeaning`, `ContinuumCoulomb_Quantum_QuantumPaddedLabelProgram`, `ContinuumCoulomb_Quantum_QuantumPaddedLabelTable`, `ContinuumCoulomb_Quantum_QuantumPaddedLocal`, `ContinuumCoulomb_Quantum_QuantumPaddedPauli`, `ContinuumCoulomb_Quantum_QuantumPaddedSampling`, `ContinuumCoulomb_Quantum_QuantumPaddedTableProgram`, `ContinuumCoulomb_Quantum_QuantumParallelRouteSearch`, `ContinuumCoulomb_Quantum_QuantumPathIteratedBound`, `ContinuumCoulomb_Quantum_QuantumPathPolynomialBound`, `ContinuumCoulomb_Quantum_QuantumPathScaleProgram`, `ContinuumCoulomb_Quantum_QuantumPauliBasis`, `ContinuumCoulomb_Quantum_QuantumPauliExpansion`, `ContinuumCoulomb_Quantum_QuantumPauliExtend`, `ContinuumCoulomb_Quantum_QuantumPauliLocal`, `ContinuumCoulomb_Quantum_QuantumPauliMonomial`, `ContinuumCoulomb_Quantum_QuantumPauliParity`, `ContinuumCoulomb_Quantum_QuantumPauliRounding`, `ContinuumCoulomb_Quantum_QuantumPauliSingle`, `ContinuumCoulomb_Quantum_QuantumPauliSplit`, `ContinuumCoulomb_Quantum_QuantumPlanarTapeSupport`, `ContinuumCoulomb_Quantum_QuantumPolarizedSubdivision`, `ContinuumCoulomb_Quantum_QuantumPolarizedThird`, `ContinuumCoulomb_Quantum_QuantumPortCrossingSelection`, `ContinuumCoulomb_Quantum_QuantumPortPairing`, `ContinuumCoulomb_Quantum_QuantumPortRankProgram`, `ContinuumCoulomb_Quantum_QuantumRawCorrectness`, `ContinuumCoulomb_Quantum_QuantumRawEnvelope`, `ContinuumCoulomb_Quantum_QuantumRawExchange`, `ContinuumCoulomb_Quantum_QuantumRawFamilyCorrectness`, `ContinuumCoulomb_Quantum_QuantumRawFamilyProgram`, `ContinuumCoulomb_Quantum_QuantumRawIncidence`, `ContinuumCoulomb_Quantum_QuantumRawOutputBounds`, `ContinuumCoulomb_Quantum_QuantumRawSchedule`, `ContinuumCoulomb_Quantum_QuantumRebitLocal`, `ContinuumCoulomb_Quantum_QuantumReferenceBasis`, `ContinuumCoulomb_Quantum_QuantumReferenceBlocks`, `ContinuumCoulomb_Quantum_QuantumReferenceEdgeTable`, `ContinuumCoulomb_Quantum_QuantumReferenceEdges`, `ContinuumCoulomb_Quantum_QuantumReferenceLocal`, `ContinuumCoulomb_Quantum_QuantumReferenceReal`, `ContinuumCoulomb_Quantum_QuantumReferenceTerms`, `ContinuumCoulomb_Quantum_QuantumRetainedCrossing`, `ContinuumCoulomb_Quantum_QuantumRouteLanes`, `ContinuumCoulomb_Quantum_QuantumRouteLeaf`, `ContinuumCoulomb_Quantum_QuantumRoutingProgram`, `ContinuumCoulomb_Quantum_QuantumRowTransfer`, `ContinuumCoulomb_Quantum_QuantumSampleAssembly`, `ContinuumCoulomb_Quantum_QuantumSampleBudget`, `ContinuumCoulomb_Quantum_QuantumSamplePrecision`, `ContinuumCoulomb_Quantum_QuantumScalarReindex`, `ContinuumCoulomb_Quantum_QuantumScaledDirection`, `ContinuumCoulomb_Quantum_QuantumSortedTime`, `ContinuumCoulomb_Quantum_QuantumSpacedListProgram`, `ContinuumCoulomb_Quantum_QuantumSparseEndpoint`, `ContinuumCoulomb_Quantum_QuantumSpatialClockTerms`, `ContinuumCoulomb_Quantum_QuantumSpatialPortProgram`, `ContinuumCoulomb_Quantum_QuantumSpatialSubdivision`, `ContinuumCoulomb_Quantum_QuantumStageStep`, `ContinuumCoulomb_Quantum_QuantumSubdivisionSites`, `ContinuumCoulomb_Quantum_QuantumSupportDedup`, `ContinuumCoulomb_Quantum_QuantumSupportLookup`, `ContinuumCoulomb_Quantum_QuantumSweepCells`, `ContinuumCoulomb_Quantum_QuantumSweepCircuit`, `ContinuumCoulomb_Quantum_QuantumSweepCoverage`, `ContinuumCoulomb_Quantum_QuantumSweepCursor`, `ContinuumCoulomb_Quantum_QuantumSweepIndex`, `ContinuumCoulomb_Quantum_QuantumSweepProgram`, `ContinuumCoulomb_Quantum_QuantumTaggedStage`, `ContinuumCoulomb_Quantum_QuantumTensorMatrix`, `ContinuumCoulomb_Quantum_QuantumTensorPair`, `ContinuumCoulomb_Quantum_QuantumTermTime`, `ContinuumCoulomb_Quantum_QuantumTimeCongestion`, `ContinuumCoulomb_Quantum_QuantumTimeGrouping`, `ContinuumCoulomb_Quantum_QuantumTransferSweep`, `ContinuumCoulomb_Quantum_QuantumTranslatedInternalSeparation`, `ContinuumCoulomb_Quantum_QuantumUnaryPrefix`, `ContinuumCoulomb_Quantum_QuantumUnaryPrefixCertificate`, `ContinuumCoulomb_Quantum_QuantumWalkErasure`, `ContinuumCoulomb_Quantum_QuantumWalkErasureProgram`, `ContinuumCoulomb_Quantum_QuantumWalkSeek`, `ContinuumCoulomb_Quantum_QuantumWireGrid`, `ContinuumCoulomb_Quantum_QuantumWireSwap`, `ContinuumCoulomb_Quantum_QuantumXZFamily`, `ContinuumCoulomb_Quantum_QuantumXZFamilySplit`, `ContinuumCoulomb_Quantum_QuantumXZSample`, `ContinuumCoulomb_Quantum_QuantumXZSubdivision`, `ContinuumCoulomb_Quantum_QuantumXZTerms`, `ContinuumCoulomb_Quantum_QuantumYYFactor`, `ContinuumCoulomb_Reduction_Model`, `ContinuumCoulomb_Reduction_SourcePauli`, `ContinuumCoulomb_Reduction_UniformQuadrature`, `ContinuumCoulomb_Reduction_UniformSamples`, `CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv`, `CoulombRadii_FieldAnalysis_FermionicCoefficients`, `CoulombRadii_FieldAnalysis_SlotTensor`, `CoulombRadii_FormDomain_CubeGradient`, `CoulombRadii_FormDomain_HardyMollifier`, `CoulombRadii_FormDomain_SmoothCompact`, `QuantumFactoring_BitStackBoundedUnary`.
--
--   **Imports.** It imports the published bundle `Def_ContinuumCoulombHardness`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ092A005`, `OAIQ092A006`, `OAIQ092A007` and `OAIQ092A011`; the statement `OAI.ContinuumCoulomb.qmaXZSubdivision_accuracy`.
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
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
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
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
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
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.UpperLower.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
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
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_ContinuumCoulombHardness

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateL2
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
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateL2`

`L²` translation estimates for Euclidean `C¹_c` functions (and derived `H¹`) under invariant
measures.

This file lifts the pointwise fundamental-theorem-of-calculus bound from
`Euclidean.TranslationEstimate` to an `L²` bound using Tonelli and the measure-preserving property
of translations.

## Main results

- `enorm_translateL2_sub_toL2_le`: for `f ∈ C¹_c`, `‖τ_a f - f‖₂ ≤ ‖a‖ · ‖∇f‖₂` (as an `ℝ≥0∞`
  inequality on `L²` norms), under a right-invariant measure.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance instMeasurableSpaceE_SobolevEuclideanTranslationEstimateL2 :
    MeasurableSpace E := borel E

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_ChargeTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact energy of a virtual hole and double occupancy

A single hop out of the singly occupied subspace creates one empty site and
one doubly occupied site. The full long-range charge penalty on that
configuration is exactly `U - V i j`, so intersite direct repulsion remains
in the superexchange denominator.
-/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def chargeTransferOccupation {m : ℕ} (hole double : Fin m) : Fin m → Fin 3 :=
  Function.update (Function.update (fun _ => 1) hole 0) double 2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_UniformQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative left-endpoint quadrature bound, including errors in the
sample values. It will be applied successively to the fixed-dimensional
truncated heat integral. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.UniformQuadrature

def node (a h : ℝ) (i : ℕ) : ℝ := a + (i : ℝ) * h

end ContinuumCoulomb.UniformQuadrature

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_UniformSamples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Left-endpoint quadrature with a finite sequence of computed samples. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.UniformQuadrature

def sampleSum (h : ℝ) (N : ℕ) (v : ℕ → ℝ) : ℝ :=
  h * ∑ i ∈ Finset.range N, v i

end ContinuumCoulomb.UniformQuadrature

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RectangleQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative tensor quadrature in two coordinates, with independent
coordinate moduli and errors in each computed sample. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.UniformQuadrature

def rectangleSum (hx hy : ℝ) (Nx Ny : ℕ) (v : ℕ → ℕ → ℝ) : ℝ :=
  sampleSum hx Nx (fun i => sampleSum hy Ny (v i))

end ContinuumCoulomb.UniformQuadrature

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteCubeQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product-interval integration and its uniform coordinate modulus. The
application uses dimension six; the recursion only avoids repeating six
identical one-dimensional estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.UniformQuadrature

def cubeMem {n : ℕ} (a b : ℝ) (v : Fin n → ℝ) : Prop := ∀ i, v i ∈ Set.Icc a b

def cubeModulus {n : ℕ} (a b L : ℝ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ v, cubeMem a b v → ∀ w, cubeMem a b w →
    |f v - f w| ≤ L * ∑ i, |v i - w i|

def cubeIntegral (a b : ℝ) : (n : ℕ) → ((Fin n → ℝ) → ℝ) → ℝ
  | 0, f => f Fin.elim0
  | n + 1, f => ∫ x in a..b, cubeIntegral a b n (fun v => f (Fin.cons x v))

def cubeSample (h : ℝ) (N : ℕ) : (n : ℕ) → ((Fin n → ℕ) → ℝ) → ℝ
  | 0, v => v Fin.elim0
  | n + 1, v => sampleSum h N (fun i => cubeSample h N n (fun w => v (Fin.cons i w)))

end ContinuumCoulomb.UniformQuadrature

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_Spin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The two-spin Heisenberg interaction

The basis order is `↑↑, ↑↓, ↓↑, ↓↓`.  The matrix below is
`X ⊗ X + Y ⊗ Y + Z ⊗ Z = 2 SWAP - I` in that basis.
The exact singlet/triplet computation supplies the interaction bound
used when rounding or deleting source coefficients in both continuum
Coulomb manuscripts (their sections on rational source normalization).
-/

namespace ContinuumCoulomb

open Matrix Complex
open scoped BigOperators

def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Tensor product written in the fixed four-state computational basis. -/
def twoSpinTensor (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  !![A 0 0 * B 0 0, A 0 0 * B 0 1, A 0 1 * B 0 0, A 0 1 * B 0 1;
     A 0 0 * B 1 0, A 0 0 * B 1 1, A 0 1 * B 1 0, A 0 1 * B 1 1;
     A 1 0 * B 0 0, A 1 0 * B 0 1, A 1 1 * B 0 0, A 1 1 * B 0 1;
     A 1 0 * B 1 0, A 1 0 * B 1 1, A 1 1 * B 1 0, A 1 1 * B 1 1]

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_Singlet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact singlet mediator calculations

The positive-spin conversion uses the singlet mediator of Piddock–Montanaro,
*The complexity of antiferromagnetic interactions and 2D lattices*, Quantum
Information and Computation 17 (2017), Section 2.4 and Lemma 5.
The Pauli contractions and penalty identities use an unnormalized singlet
vector, whose expectation values are twice the normalized values.
-/

noncomputable section

namespace ContinuumCoulomb

open Matrix
open scoped BigOperators

def pauli (μ : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![pauliX, pauliY, pauliZ] μ

def firstPauli (μ : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  twoSpinTensor (pauli μ) 1

def secondPauli (μ : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  twoSpinTensor 1 (pauli μ)

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

theorem bellScale_sq : bellScale ^ 2 = (1 / 2 : ℂ) := by
  unfold bellScale
  rw [← Complex.ofReal_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  norm_num

@[simp] theorem bellScale_star : star bellScale = bellScale := by
  simp [bellScale]

def bellRaw : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 1; 1, 0, 1, 0; -1, 0, 1, 0; 0, 1, 0, -1]

def bellMatrix : Matrix (Fin 4) (Fin 4) ℂ := bellScale • bellRaw

def bellTransform (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  bellMatrix.conjTranspose * M * bellMatrix

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

/-- Actual Pauli action on either member of a mediator pair in Bell coordinates. -/
def bellMemberPauli (member : Fin 2) (μ : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  if member = 0 then bellTransform (firstPauli μ) else bellTransform (secondPauli μ)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_HardyMollifier
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

noncomputable def hardyMollifier {n : ℕ} (k : ℕ) : ContDiffBump (0 : Configuration n) where
  rIn := 1 / ((k : ℝ) + 1)
  rOut := 2 / ((k : ℝ) + 1)
  rIn_pos := one_div_pos.mpr (by positivity)
  rIn_lt_rOut := div_lt_div_of_pos_right (by norm_num) (by positivity)

lemma complex_norm_sq_components (z : ℂ) : ‖z‖^2 = z.re^2 + z.im^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Full spinful continuum Coulomb energy

Nuclear data and electronic states use the weak H¹ domain and translated
Hardy bounds. Antisymmetry
permutes spin and position together. No orbital projection or spin sector is
imposed. The bottom takes values in `EReal` so its definition does not assume
existence of a normalized state or a minimizing eigenvector.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace ContinuumCoulomb

/-- The unit-to-binary inclusion preserves the entire variational energy. -/
theorem unit_groundEnergy_eq (d : UnitNuclearData) :
    groundEnergy d.toNuclearData = unitGroundEnergy d := rfl

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

noncomputable def tensorOrbital {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ) (b : Fin n → α) (s : Spins n) (x : Configuration n) : ℂ :=
  ∏ i, v (b i) (position x i) (s i)

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

noncomputable def configurationMeasurableEquiv (n : ℕ) :
    Configuration n ≃ᵐ (Fin n → Space) :=
  ((MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)).symm.trans
    (MeasurableEquiv.curry (Fin n) (Fin 3) ℝ)).trans
    (MeasurableEquiv.piCongrRight fun _ => MeasurableEquiv.toLp 2 (Fin 3 → ℝ))

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_SmoothCompact
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
namespace Coulomb

noncomputable def positionCLM {n : ℕ} (i : Fin n) : Configuration n →L[ℝ] Space :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun b : Fin 3 =>
      (EuclideanSpace.proj (i,b) : Configuration n →L[ℝ] ℝ))

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowJetCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coordinates for spatial jets in dimension three. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb

abbrev SpatialJet (n : ℕ) := Position [×n]→L[ℝ] Position

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabLineIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered-interval comparison for the actual one-coordinate Coulomb
integrals. It is the coordinatewise monotonicity step in the slab estimate. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def centeredLineIntegral (f : ℝ → ℝ) (H x : ℝ) : ℝ :=
  ∫ t in (x-H)..(x+H), f t

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabCoordinates
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

abbrev SlabTriple := ℝ × (ℝ × ℝ)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CappedCoulombKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded Lipschitz kernel for literal Coulomb quadrature. The original
singular potential differs only inside the cap radius; the next theorem
controls that error by the actual Coulomb mass of the small ball. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def cappedCoulombKernel (ε : ℝ) (x : Position) : ℝ := (max ε ‖x‖)⁻¹

def cappedCoulombPotential (ε : ℝ) (ρ : Position → ℝ) (x : Position) : ℝ :=
  ∫ y, cappedCoulombKernel ε (x - y) * ρ y

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

theorem sourceTensor_mul (n : ℕ) (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    sourceTensor n M * sourceTensor n N = sourceTensor n (fun i => M i * N i) := by
  ext s t
  simp only [Matrix.mul_apply, sourceTensor, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => M i (s i) a * N i a (t i))).symm

def sourceLocalPauli (n : ℕ) (i : Fin n) (μ : Fin 3) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  sourceTensor n (fun k => if k = i then pauli μ else 1)

def sourceSpectatorDelta (n : ℕ) (i j : Fin n) (s t : SourceSpinBasis n) : ℂ :=
  ∏ k ∈ (Finset.univ.erase i).erase j, if s k = t k then (1 : ℂ) else 0

theorem sourceSpectatorDelta_eq_zero (n : ℕ) (i j : Fin n) (s t : SourceSpinBasis n)
    (hst : ¬∀ k, k ≠ i → k ≠ j → s k = t k) : sourceSpectatorDelta n i j s t = 0 := by
  classical
  push Not at hst
  obtain ⟨k, hki, hkj, hne⟩ := hst
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hkj,
    Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩⟩)
  simp [hne]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PolynomialTimeSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial-time TM2 program has polynomial output bit length. The
constant below counts the pushes in its finite program text, rather than
assuming an output-size estimate as an additional complexity axiom. -/

namespace ContinuumCoulomb
open Turing StateTransition
open scoped BigOperators

namespace TM2Size

/-- Maximum number of pushes along one finite statement branch. -/
def pushes {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

theorem stepAux_stack_length {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes q := by
  induction q generalizing v S with
  | push j f q ih =>
    have h := ih v (Function.update S j (f v :: S j))
    have hu : (Function.update S j (f v :: S j) k).length ≤ (S k).length + 1 := by
      by_cases hj : k = j
      · subst k; simp
      · simp [Function.update_of_ne hj]
    change ((TM2.stepAux q v (Function.update S j (f v :: S j))).stk k).length ≤ _
    unfold pushes
    omega
  | peek j f q ih => exact ih _ _
  | pop j f q ih =>
    have h := ih (f v (S j).head?) (Function.update S j (S j).tail)
    have hu : (Function.update S j (S j).tail k).length ≤ (S k).length := by
      by_cases hj : k = j
      · subst k; simp
      · simp [Function.update_of_ne hj]
    change ((TM2.stepAux q (f v (S j).head?) (Function.update S j (S j).tail)).stk k).length ≤ _
    unfold pushes
    omega
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr =>
    change ((cond (f v) (TM2.stepAux q v S) (TM2.stepAux r v S)).stk k).length ≤ _
    cases hf : f v
    · simpa only [hf, Bool.cond_false, pushes] using (ihr v S).trans
        (Nat.add_le_add_left (le_max_right (pushes q) (pushes r)) (S k).length)
    · simpa only [hf, Bool.cond_true, pushes] using (ihq v S).trans
        (Nat.add_le_add_left (le_max_left (pushes q) (pushes r)) (S k).length)
  | goto f => simp [pushes, TM2.stepAux]
  | halt => simp [pushes, TM2.stepAux]

/-- A finite program has a fixed bound on pushes in one machine step. -/
def programPushes (tm : FinTM2) : ℕ := by
  letI := tm.ΛFin
  exact Finset.univ.sup (fun l => pushes (tm.m l))

theorem step_stack_length (tm : FinTM2) (a b : tm.Cfg) (k : tm.K)
    (h : tm.step a = some b) :
    (b.stk k).length ≤ (a.stk k).length + programPushes tm := by
  let := tm.ΛFin
  cases a with
  | mk l v S =>
    cases l with
    | none => simp [FinTM2.step, TM2.step] at h
    | some l =>
      have hb : TM2.stepAux (tm.m l) v S = b := by
        exact Option.some.inj h
      rw [← hb]
      exact (stepAux_stack_length (tm.m l) v S k).trans
        (Nat.add_le_add_left (Finset.le_sup (f := fun l => pushes (tm.m l)) (Finset.mem_univ l)) _)

theorem iterate_stack_length (tm : FinTM2) (n : ℕ) (a b : tm.Cfg) (k : tm.K)
    (h : (fun x : Option tm.Cfg => x.bind tm.step)^[n] (some a) = some b) :
    (b.stk k).length ≤ (a.stk k).length + n * programPushes tm := by
  induction n generalizing b with
  | zero =>
    have hab : a = b := by simpa only [Function.iterate_zero_apply, Option.some.injEq] using h
    subst b
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    cases he : (fun x : Option tm.Cfg => x.bind tm.step)^[n] (some a) with
    | none => simp only [he, Option.bind_none] at h; contradiction
    | some c =>
      have hs : tm.step c = some b := by simpa only [he, Option.bind_some] using h
      have hc := ih c he
      have hb := step_stack_length tm c b k hs
      rw [Nat.succ_mul]
      omega

theorem init_stack_length (tm : FinTM2) (L : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((initList tm L).stk k).length ≤ L.length := by
  by_cases hk : k = tm.k₀
  · subst k; simp [initList]
  · simp [initList, hk]

/-- Bit output length is bounded directly from a genuine polynomial-time
certificate; this is needed when composing the hardness reduction. -/
theorem output_length {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤ (ea a).length + h.time.eval (ea a).length * programPushes h.tm := by
  have ho := h.outputsFun a
  have hi : ((initList h.tm (List.map h.inputAlphabet.invFun (ea a))).stk h.tm.k₁).length ≤
      (ea a).length := by
    simpa only [List.length_map] using
      init_stack_length h.tm (List.map h.inputAlphabet.invFun (ea a)) h.tm.k₁
  have hv := iterate_stack_length h.tm ho.steps
    (initList h.tm (List.map h.inputAlphabet.invFun (ea a)))
    (haltList h.tm (List.map h.outputAlphabet.invFun (eb (f a)))) h.tm.k₁ ho.evals_in_steps
  have hout : ((haltList h.tm (List.map h.outputAlphabet.invFun (eb (f a)))).stk h.tm.k₁).length =
      (eb (f a)).length := by simp [haltList]
  rw [hout] at hv
  exact hv.trans (Nat.add_le_add hi (Nat.mul_le_mul_right _ ho.steps_le_m))

end TM2Size
end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabOriginQuadrature
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

def point (H S : ℝ) (v : Fin 3 → ℝ) : Position :=
  WithLp.toLp 2 ![H*v 0,H*v 1,S*v 2]

def integrand (ε H S : ℝ) (v : Fin 3 → ℝ) : ℝ := cappedCoulombKernel ε (point H S v)

end ContinuumCoulomb.SlabOriginQuadrature

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

def spatialStep (N : ℕ) : ℚ := 2 / (N : ℚ)

end ContinuumCoulomb.RationalHeatBox

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabBoxSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational slab dimensions with separate unary magnitude bounds. This
covers exactly the half-cell boundary of the odd centered grid. -/

noncomputable section
namespace ContinuumCoulomb.SlabBoxSchedule

def bound (rho Q N : ℕ) (H S : ℝ) : ℝ :=
  (rho:ℝ)*H^2*S*8*(3*((Q:ℝ)^2*(H+S))*(2/(N:ℝ))+
    (Q:ℝ)^2*(2:ℝ)⁻¹^N)+(rho:ℝ)*(2*Real.pi*((Q:ℝ)⁻¹)^2)

end ContinuumCoulomb.SlabBoxSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CubeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Euclidean mesh cells: volume, radius, node containment, and
disjoint interiors. These retain the volume normalization of the Gauss rule. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def positionCube (b : Position) (h : ℝ) : Set Position :=
  WithLp.ofLp ⁻¹' Set.Icc (fun i => b i-h/2) (fun i => b i+h/2)

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

noncomputable def slotTensor {A : Type*} {n : ℕ} (v d : Fin n → A → ℂ)
    (p : Equiv.Perm (Fin n)) (i : Fin n) (x : Fin n → A) : ℂ :=
  ∏ j, if j = i then d (p j) (x j) else v (p j) (x j)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_CubeGradient
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
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma positionCLM_single {n : ℕ} (i j : Fin n) (b : Fin 3) :
    positionCLM j (EuclideanSpace.single (i,b) 1) =
      if j = i then EuclideanSpace.single b 1 else 0 := by
  ext c
  by_cases h : j = i
  · subst j
    simp [positionCLM]
  · simp [positionCLM, h]

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_TransportedFarQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local fourth-order error with the nondecaying transport correction
charged only to cells meeting the compact well support. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb

def cellHits (E : Set Position) (b : Position) (h : ℝ) : ℝ :=
  if ∃ z ∈ positionCube b h, z ∈ E then 1 else 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_AtomicOutputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed one-electron outputs for the decidable one-spin source branch.
The only spectral input is the precisely stated published hydrogen bottom. -/

noncomputable section
namespace ContinuumCoulomb
open MeasureTheory

def atomicData : UnitNuclearData where
  nuclei := 1
  nuclei_pos := by decide
  position := fun _ => 0
  distinct := fun _ _ _ => Subsingleton.elim _ _
  electrons := 1
  electrons_pos := by decide

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
def boundedPotentialForm {n : ℕ} (V : Configuration n → ℝ) (u : Coulomb.H1Vector n) : ℝ :=
  Coulomb.kinetic u + ∑ s, ∫ x, V x * ‖u.value s x‖^2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CappedCoulombTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-box truncation of the bounded Coulomb integral. The bound is
uniform in the displacement and uses only the discarded density masses. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def cappedPairIntegrand (ε : ℝ) (shift : Position) (f g : Position → ℝ)
    (p : Position × Position) : ℝ :=
  f p.1 * g p.2 * cappedCoulombKernel ε (p.1 - p.2 - shift)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ClassicalTensor
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

theorem tensorOrbital_C1 {n : ℕ} {α : Type*} (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s)) (p : Fin n → α) (s : SpinConfiguration n) :
    ContDiff ℝ 1 (Coulomb.tensorOrbital v p s) := by
  unfold Coulomb.tensorOrbital
  apply contDiff_prod
  intro i _
  exact (hv (p i) (s i)).comp (Coulomb.positionCLM i).contDiff

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactTemplates
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

def contactSlopeHeight (c : ℝ) : ℝ := Real.sqrt (1 - c ^ 2)

def contactStepX (c : ℝ) (k : ℕ) : ℝ :=
  if k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 6 then c else 1

def contactStepY (c : ℝ) (k : ℕ) : ℝ :=
  if k = 2 ∨ k = 3 then contactSlopeHeight c
  else if k = 5 ∨ k = 6 then -contactSlopeHeight c else 0

theorem contactSlopeHeight_sq {c : ℝ} (hc : -1 ≤ c) (hc' : c ≤ 1) :
    contactSlopeHeight c ^ 2 = 1 - c ^ 2 := by
  apply Real.sq_sqrt
  nlinarith

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

def adjustedContactStepY (h : ℝ) (k : ℕ) : ℝ :=
  if k = 2 ∨ k = 3 then h else if k = 5 ∨ k = 6 then -h else 0

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

def contactGadgetSlope (negative : Bool) : ℝ := if negative then 7 / 8 else 3 / 4

def contactGadgetSpan (negative : Bool) (central : ℝ) : ℝ :=
  if negative then 17 / 2 else (17 - central) / 2

def contactGadgetRightOrigin (negative : Bool) (central : ℝ) : ℝ :=
  if negative then 17 / 2 else (17 + central) / 2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CubeMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The recursive quadrature integral is the actual product Lebesgue
integral on the cube. This identifies the six-coordinate computation with
the finite Coulomb box, rather than a separately defined integral. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.UniformQuadrature

def cubeMeasure (a b : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc a b))

instance cubeMeasure_finite (a b : ℝ) (n : ℕ) : IsFiniteMeasure (cubeMeasure a b n) := by
  unfold cubeMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end ContinuumCoulomb.UniformQuadrature

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OrbitalCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Expanding smooth cutoffs for the actual orbitals. Their first four
jets are bounded independently of the radius and center. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

def orbitalCutoffBump : ContDiffBump (0 : Position) := ⟨1,2,by norm_num,by norm_num⟩

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

def UnitCoulomb.toBinary (d : UnitCoulomb) : BinaryCoulomb where
  nuclei := d.nuclei.map (fun r => (r, 1))
  electrons := d.electrons
  lower := d.lower
  upper := d.upper

theorem UnitCoulomb.toBinary_valid (d : UnitCoulomb) (h : d.Valid) : d.toBinary.Valid := by
  dsimp only [UnitCoulomb.toBinary]
  refine {
    nuclei_pos := by simpa only [UnitCoulomb.toBinary, List.length_map] using h.nuclei_pos
    electrons_pos := h.electrons_pos
    positions := ?_
    distinct := ?_
    charge_pos := ?_
    lower_denominator := h.lower_denominator
    upper_denominator := h.upper_denominator
    gap := h.gap }
  · intro a
    change ((d.nuclei.map (fun r => (r, (1 : ℕ)))).get a).1.Valid
    simp only [List.get_eq_getElem, List.getElem_map]
    exact h.positions ⟨a.val, by simpa only [List.length_map] using a.isLt⟩
  · intro a b hab
    change ((d.nuclei.map (fun r => (r, (1 : ℕ)))).get a).1.value =
      ((d.nuclei.map (fun r => (r, (1 : ℕ)))).get b).1.value at hab
    simp only [List.get_eq_getElem, List.getElem_map] at hab
    have h' := h.distinct (a₁ := ⟨a.val, by simpa only [List.length_map] using a.isLt⟩)
      (a₂ := ⟨b.val, by simpa only [List.length_map] using b.isLt⟩) hab
    exact Fin.ext (congrArg (fun x : Fin d.nuclei.length => x.val) h')
  · intro a
    change 0 < ((d.nuclei.map (fun r => (r, (1 : ℕ)))).get a).2
    simp only [List.get_eq_getElem, List.getElem_map]
    exact Nat.zero_lt_one

theorem nuclearData_ext (d e : NuclearData) (hn : d.nuclei=e.nuclei)
    (hp : ∀ i, d.position i=e.position (Fin.cast hn i))
    (hz : ∀ i, d.charge i=e.charge (Fin.cast hn i)) (he : d.electrons=e.electrons) : d=e := by
  rcases d with ⟨nd,hnd,pd,hd,zd,hzd,ed,hed⟩
  rcases e with ⟨ne,hne,pe,he',ze,hze,ee,hee⟩
  dsimp only at hn hp hz he
  subst ne
  simp only [Fin.cast_refl, id_eq] at hp hz
  have hp' := funext hp
  have hz' := funext hz
  subst pe
  subst ze
  subst ee
  rfl

theorem UnitCoulomb.toBinary_toData (d : UnitCoulomb) (h : d.Valid) :
    d.toBinary.toData (d.toBinary_valid h) = (d.toData h).toNuclearData := by
  apply nuclearData_ext _ _ (by exact List.length_map (fun r => (r, (1 : ℕ))))
  · intro i
    dsimp only [UnitCoulomb.toBinary, BinaryCoulomb.toData, UnitCoulomb.toData,
      UnitNuclearData.toNuclearData] at i ⊢
    simp only [List.get_eq_getElem, List.getElem_map, Fin.val_cast]
  · intro i
    dsimp only [UnitCoulomb.toBinary, BinaryCoulomb.toData, UnitCoulomb.toData,
      UnitNuclearData.toNuclearData] at i ⊢
    simp only [List.get_eq_getElem, List.getElem_map]
  · rfl

noncomputable section

theorem UnitCoulomb.toBinary_energy (d : UnitCoulomb) (h : d.Valid) :
    groundEnergy (d.toBinary.toData (d.toBinary_valid h)) = unitGroundEnergy (d.toData h) := by
  rw [d.toBinary_toData h, unit_groundEnergy_eq]

end
end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackBoundedUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def unaryDecodeStep (s : ℕ×ℕ) : ℕ×ℕ := if s.1=0 then s else (s.1-1,s.2+1)
lemma unaryDecodeStep_iterate (k : ℕ) (s : ℕ×ℕ) :
    (unaryDecodeStep^[k]) s=(s.1-k,s.2+min k s.1) := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>
    rw [Function.iterate_succ_apply,ih]
    unfold unaryDecodeStep
    split
    · rename_i hz
      apply Prod.ext <;> dsimp only <;> omega
    · rename_i hz
      apply Prod.ext <;> dsimp only <;> omega
end ExactQuantumFactoring.BitStackProgram

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

abbrev positionListCodec := BinaryEncoding.list binaryPositionCodec
abbrev nucleusCodec := BinaryEncoding.pair binaryPositionCodec BinaryEncoding.natural
abbrev nucleusListCodec := BinaryEncoding.list nucleusCodec

end ContinuumCoulomb.UnitBinaryProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateUnitary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact unitarity of the fixed verifier gates, needed for the
circuit-to-Hamiltonian construction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

theorem qmaHadamard_gram : qmaHadamard.conjTranspose * qmaHadamard = 1 := by
  have hs : (starRingEnd ℂ) bellScale = bellScale := bellScale_star
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [qmaHadamard,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fin.sum_univ_succ,bellScale_star,star_mul,hs] <;>
    ring_nf <;> norm_num [bellScale_sq,hs]

theorem sourceTensor_conjTranspose (n : ℕ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (sourceTensor n M).conjTranspose = sourceTensor n (fun i => (M i).conjTranspose) := by
  ext s t
  simp [sourceTensor,Matrix.conjTranspose_apply]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_ClockPathBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary quantitative propagation estimates for the finite clock.
They compare every clock slice to its initial slice. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def clockPathEnergy {E : Type*} [NormedAddCommGroup E] (f : ℕ → E) (T : ℕ) : ℝ :=
  ∑ i ∈ Finset.range T, ‖f (i+1)-f i‖^2

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

def qmaClockMiddle (T : ℕ) (i : Fin T) : Fin (T+2) := ⟨i.val+1,by omega⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal controls and changes between explicit qubit coordinate sets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaJoinMatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (B : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) :
    Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ :=
  (A ⊗ₖ B).submatrix (Equiv.sumArrowEquivProdArrow ι κ (Fin 2))
    (Equiv.sumArrowEquivProdArrow ι κ (Fin 2))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actions of local flips and spectator-identity tensor factors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaBitFlip (i : ι) (s : ι → Fin 2) : ι → Fin 2 :=
  Function.update s i (Equiv.swap (0:Fin 2) 1 (s i))

def qmaBitFlipMatrix (i : ι) : Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  fun s t => if s = qmaBitFlip i t then 1 else 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalPenalties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The clock and endpoint penalties are explicit one- and two-qubit terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaBitDiagonal (i : ι) (f : Fin 2 → ℂ) : Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  Matrix.diagonal (fun s => f (s i))

def qmaPairDiagonal (i j : ι) (f : Fin 2 → Fin 2 → ℂ) :
    Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  Matrix.diagonal (fun s => f (s i) (s j))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Pauli expansion on the bounded supports of the circuit terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaPauli (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ := ![1,pauliX,pauliY,pauliZ] i

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaPauliWord (w : ι → Fin 4) : Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  fun s t => ∏ i, qmaPauli (w i) (s i) (t i)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficients of the actual small local matrices in the Pauli basis. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaPauliCoefficient (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (w : ι → Fin 4) : ℂ :=
  ((2:ℂ)^Fintype.card ι)⁻¹ * ∑ s, ∑ t, A s t*qmaPauliWord w t s

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A real Hermitian matrix contains only Pauli words with an even number
of imaginary Y factors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaPauliYCount (w : ι → Fin 4) : ℕ := (Finset.univ.filter (fun i => w i = 2)).card

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact supports and tensor joins of the Pauli words used in the reduction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def qmaPauliSupport (w : ι → Fin 4) : Finset ι := Finset.univ.filter (fun i => w i ≠ 0)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balanced disjoint factorizations for the two subdivision stages. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaPauliRestrict (S : Finset ι) (w : ι → Fin 4) : ι → Fin 4 :=
  fun i => if i ∈ S then w i else 0

theorem qmaPauliRestrict_support (S : Finset ι) (w : ι → Fin 4) :
    qmaPauliSupport (qmaPauliRestrict S w) ⊆ S := by
  intro i hi
  by_contra h
  simp [qmaPauliSupport,qmaPauliRestrict,h] at hi

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensoring with fresh mediators adds precisely their explicit supports. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem qmaJoinMatrix_mul (A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (C D : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) :
    qmaJoinMatrix (A*B) (C*D) = qmaJoinMatrix A C*qmaJoinMatrix B D := by
  unfold qmaJoinMatrix
  rw [Matrix.submatrix_mul_equiv,← Matrix.mul_kronecker_mul]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliExtend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extending a Pauli word by identities is exactly the local tensor lift. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaPauliExtend (S : Finset ι) (w : {i // i ∈ S} → Fin 4) : ι → Fin 4 :=
  fun i => if hi : i ∈ S then w ⟨i,hi⟩ else 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliMonomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse actions of the physical Pauli matrices, retaining a rational part. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaPauliBit (μ : Fin 3) (a : Fin 2) : Fin 2 :=
  if μ = 2 then a else Equiv.swap 0 1 a

def qmaPhysicalPauliSign (μ : Fin 3) (a : Fin 2) : ℚ :=
  if μ = 0 then 1 else if a = 0 then (if μ = 1 then -1 else 1)
    else (if μ = 1 then 1 else -1)

def qmaPauliPhase (μ : Fin 3) : ℂ := if μ = 1 then Complex.I else 1

theorem qmaPauli_monomial (μ : Fin 3) (a b : Fin 2) :
    pauli μ a b = qmaPauliPhase μ*(qmaPhysicalPauliSign μ a:ℂ)*
      (if qmaPauliBit μ a = b then 1 else 0) := by
  fin_cases μ <;> fin_cases a <;> fin_cases b <;>
    simp [pauli,pauliX,pauliY,pauliZ,qmaPauliBit,qmaPhysicalPauliSign,qmaPauliPhase,
      Equiv.swap_apply_def, Fin.ext_iff] <;> norm_num

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

theorem qmaQubit_fin {work : ℕ} (i : Fin (work+1)) : qmaQubit work i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTransferSweep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact sweeps of disjoint three-CNOT wire transfers. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

def QMATransferDisjoint {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2

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

def qmaRowPairs {n work : ℕ} (l r : Fin n → Fin (work+1)) :
    List (Fin (work+1) × Fin (work+1)) := List.ofFn (fun i => (l i,r i))

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

abbrev qmaGridWork (rows width : ℕ) : ℕ := width+rows*(width+1)

def qmaGridQubit (rows width : ℕ) (r : Fin (rows+1)) (i : Fin (width+1)) :
    Fin (qmaGridWork rows width+1) :=
  ⟨r.val*(width+1)+i.val,by
    have hr : r.val ≤ rows := Nat.le_of_lt_succ r.isLt
    have hi : i.val ≤ width := Nat.le_of_lt_succ i.isLt
    have hm := Nat.mul_le_mul_right (width+1) hr
    unfold qmaGridWork
    omega⟩

theorem qmaGridQubit_injective (rows width : ℕ) :
    Function.Injective (fun p : Fin (rows+1) × Fin (width+1) => qmaGridQubit rows width p.1 p.2) := by
  rintro ⟨r,i⟩ ⟨s,j⟩ h
  have hv : r.val*(width+1)+i.val = s.val*(width+1)+j.val := congrArg Fin.val h
  have hm := congrArg (fun k => k % (width+1)) hv
  rw [Nat.mul_add_mod_self_right,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] at hm
  have hi : i = j := Fin.ext hm
  have hr : r = s := by
    apply Fin.ext
    have hpos : 0 < width+1 := by omega
    have hij : i.val = j.val := congrArg Fin.val hi
    nlinarith
  exact Prod.ext hr hi

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepCircuit
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

def qmaSweepOrder (width row : ℕ) : Equiv.Perm (Fin (width+1)) :=
  if row % 2 = 0 then Equiv.refl _ else Fin.revPerm

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

def qmaReferencePhase : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,Complex.I]

def qmaReferenceBasis : Matrix (Fin 2) (Fin 2) ℂ := qmaReferencePhase*qmaHadamard

theorem qmaReferencePhase_gram : qmaReferencePhase.conjTranspose*qmaReferencePhase = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qmaReferencePhase,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two]

theorem qmaReferenceBasis_gram : qmaReferenceBasis.conjTranspose*qmaReferenceBasis = 1 := by
  simp only [qmaReferenceBasis,Matrix.conjTranspose_mul,mul_assoc]
  rw [←mul_assoc qmaReferencePhase.conjTranspose,qmaReferencePhase_gram,one_mul,qmaHadamard_gram]

theorem qmaReferenceBasis_y :
    qmaReferenceBasis.conjTranspose*pauliY*qmaReferenceBasis = pauliZ := by
  have hphase : qmaReferencePhase.conjTranspose*pauliY*qmaReferencePhase = pauliX := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [qmaReferencePhase,pauliY,pauliX,Matrix.mul_apply,
        Matrix.conjTranspose_apply,Fin.sum_univ_two]
  have hhad : qmaHadamard.conjTranspose*pauliX*qmaHadamard = pauliZ := by
    have hraw : (!![1,1;1,-1] : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose*
        pauliX*!![1,1;1,-1] = (2:ℂ) • pauliZ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [pauliX,pauliZ,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two]
    unfold qmaHadamard
    rw [Matrix.conjTranspose_smul,bellScale_star,smul_mul_assoc,smul_mul_assoc,
      mul_smul_comm,hraw,smul_smul,smul_smul]
    rw [show bellScale*bellScale*2 = (1:ℂ) by rw [←pow_two,bellScale_sq]; norm_num]
    exact one_smul _ _
  calc
    _ = qmaHadamard.conjTranspose*
        (qmaReferencePhase.conjTranspose*pauliY*qmaReferencePhase)*qmaHadamard := by
      simp only [qmaReferenceBasis,Matrix.conjTranspose_mul,mul_assoc]
    _ = _ := by rw [hphase,hhad]

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

def qmaZSign (b : Fin 2) : ℂ := if b = 0 then 1 else -1

theorem pauliZ_diagonal : pauliZ = Matrix.diagonal qmaZSign := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauliZ,qmaZSign]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact sector decomposition for distributed realification. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

def qmaConjugateMatrix (A : Matrix α α ℂ) : Matrix α α ℂ :=
  fun a b => star (A a b)

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

def qmaUnitFin : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv i := by fin_cases i; rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distributed reference terms are actual real Hermitian matrices. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem qmaHermitian_of_conjugated {β : Type*} [Fintype β] [DecidableEq β]
    (B M : Matrix β β ℂ) (hB : B*B.conjTranspose = 1)
    (hM : (B.conjTranspose*M*B).IsHermitian) : M.IsHermitian := by
  have he : B*(B.conjTranspose*M*B)*B.conjTranspose = M := by
    calc
      _ = (B*B.conjTranspose)*M*(B*B.conjTranspose) := by simp only [mul_assoc]
      _ = M := by rw [hB]; simp
  rw [←he]
  exact Matrix.isHermitian_mul_mul_conjTranspose B hM

omit [Fintype α] [DecidableEq α] in
theorem qmaConjugateMatrix_hermitian (A : Matrix α α ℂ) (hA : A.IsHermitian) :
    (qmaConjugateMatrix A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  exact congrArg star (hA.apply a b)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceLocal
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

def qmaDistributedRebitSites (n : ℕ) (i : Fin n) (S : Finset ι) : Finset (Fin n ⊕ ι) :=
  insert (Sum.inl i) (S.map Function.Embedding.inr)

omit [Fintype ι] in
theorem qmaDistributedRebitSites_card (n : ℕ) (i : Fin n) (S : Finset ι) :
    (qmaDistributedRebitSites n i S).card = S.card+1 := by
  simp [qmaDistributedRebitSites]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reference alignment penalty is a sum of real two-site interactions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaReferenceEdgeSites (n : ℕ) (i : Fin n) : Finset (Fin (n+1) ⊕ ι) :=
  {Sum.inl i.castSucc,Sum.inl i.succ}

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full reference Hamiltonian as explicit bounded-support real terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev QMAReferenceTerm (n : ℕ) := Fin (n+1) ⊕ Fin n

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTaggedStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact labelled row stages with at most four computation gates per column. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaNodup_filter_singleton_length {α : Type*} [DecidableEq α] (xs : List α)
    (hx : xs.Nodup) (j : α) : (xs.filter (fun i => decide (i = j))).length ≤ 1 := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    have hi := (List.nodup_cons.mp hx).1
    have ht := (List.nodup_cons.mp hx).2
    by_cases hij : i = j
    · subst i
      have hz : xs.filter (fun i => decide (i = j)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro k hk
        have hkj : k ≠ j := by intro he; subst k; exact hi hk
        simp [hkj]
      simp [hz]
    · simpa [hij] using ih ht

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

/-- Three transfer gates per column, with one gate inserted at the previous column. -/
def qmaStageCursor (cut t : ℕ) : ℕ :=
  if t < 3*cut then t/3 else if t = 3*cut then cut-1 else (t-1)/3

theorem qmaStageCursor_lt (n cut t : ℕ) (hc : 0 < cut) (hcn : cut ≤ n)
    (ht : t < 3*n+1) : qmaStageCursor cut t < n := by
  unfold qmaStageCursor
  split_ifs <;> omega

theorem qmaStageCursor_step (cut t : ℕ) (hc : 0 < cut) :
    qmaStageCursor cut t ≤ qmaStageCursor cut (t+1) ∧
      qmaStageCursor cut (t+1) ≤ qmaStageCursor cut t+1 := by
  unfold qmaStageCursor
  split_ifs <;> omega

theorem qmaStageCursor_zero (cut : ℕ) (hc : 0 < cut) : qmaStageCursor cut 0 = 0 := by
  simp [qmaStageCursor,show 0 < 3*cut by omega]

theorem qmaStageCursor_last (n cut : ℕ) (hc : 0 < cut) (hcn : cut ≤ n) :
    qmaStageCursor cut (3*n) = n-1 := by
  unfold qmaStageCursor
  split_ifs <;> omega

theorem qmaSweepOrder_near (width row : ℕ) (i j : Fin (width+1))
    (hij : i.val ≤ j.val+1) (hji : j.val ≤ i.val+1) :
    (qmaSweepOrder width row i).val ≤ (qmaSweepOrder width row j).val+1 ∧
      (qmaSweepOrder width row j).val ≤ (qmaSweepOrder width row i).val+1 := by
  unfold qmaSweepOrder
  split_ifs
  · exact ⟨hij,hji⟩
  · simp only [Fin.revPerm_apply,Fin.val_rev]
    have hi := i.isLt
    have hj := j.isLt
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

theorem qmaSweepOrder_turn (width row : ℕ) (hr : 0 < row) :
    qmaSweepOrder width row (Fin.last width) = qmaSweepOrder width (row-1) 0 := by
  have h : row%2 = 0 ∨ row%2 = 1 := by omega
  rcases h with h | h
  · have hp : (row-1)%2 = 1 := by omega
    simp [qmaSweepOrder,h,hp]
  · have hp : (row-1)%2 = 0 := by omega
    simp [qmaSweepOrder,h,hp]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every physical row is touched in a nonempty sweep, including the final row. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaGridQubit_surjective (rows width : ℕ) :
    Function.Surjective (fun p : Fin (rows+1) × Fin (width+1) => qmaGridQubit rows width p.1 p.2) := by
  apply ((Fintype.bijective_iff_injective_and_card _).mpr ⟨qmaGridQubit_injective rows width,?_⟩).2
  simp only [Fintype.card_prod,Fintype.card_fin]
  unfold qmaGridWork
  ring

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

theorem qmaList_filter_index_card {α : Type*} (xs : List α) (p : α → Bool) :
    (Finset.univ.filter (fun i : Fin xs.length => p xs[i.val])).card = (xs.filter p).length := by
  rw [Finset.card_filter]
  induction xs with
  | nil => simp
  | cons a xs ih =>
    change (∑ i : Fin (xs.length+1), if p (a::xs)[i.val] = true then 1 else 0) = _
    rw [Fin.sum_univ_succ]
    change (if p a = true then 1 else 0)+
      (∑ i : Fin xs.length, if p xs[i.val] = true then 1 else 0) = _
    rw [ih]
    by_cases ha : p a = true
    · simp [ha,Nat.add_comm]
    · have hf : p a = false := Bool.eq_false_iff.mpr ha
      simp [hf]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumClockAnchor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two endpoint clock bits and each internal clock bit have a local time anchor. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaClockAnchorIndex (T : ℕ) (hT : 0 < T) (b : Fin (T+2)) : Fin T :=
  ⟨min (b.val-1) (T-1),by omega⟩

theorem qmaClockAnchorIndex_near (T : ℕ) (hT : 0 < T) (t : Fin T) (b : Fin (T+2))
    (hb : t.val ≤ b.val ∧ b.val ≤ t.val+2) :
    (qmaClockAnchorIndex T hT b).val ≤ t.val+1 ∧ t.val ≤ (qmaClockAnchorIndex T hT b).val+1 := by
  change min (b.val-1) (T-1) ≤ t.val+1 ∧ t.val ≤ min (b.val-1) (T-1)+1
  have ht := t.isLt
  omega

theorem qmaClockAnchorIndex_fiber (T : ℕ) (hT : 0 < T) (t : Fin T) (b : Fin (T+2))
    (hb : qmaClockAnchorIndex T hT b = t) :
    b = 0 ∨ b = qmaClockMiddle T t ∨ b = Fin.last (T+1) := by
  have hv := congrArg Fin.val hb
  change min (b.val-1) (T-1) = t.val at hv
  have ht := t.isLt
  have hb' := b.isLt
  have h : b.val = 0 ∨ b.val = t.val+1 ∨ b.val = T+1 := by omega
  exact h.imp (fun h => Fin.ext h) (fun h => h.imp (fun h => Fin.ext h) (fun h => Fin.ext h))

theorem qmaClockAnchorIndex_fiber_card (T : ℕ) (hT : 0 < T) (t : Fin T) :
    (Finset.univ.filter (fun b : Fin (T+2) => qmaClockAnchorIndex T hT b = t)).card ≤ 3 := by
  have hs : Finset.univ.filter (fun b : Fin (T+2) => qmaClockAnchorIndex T hT b = t) ⊆
      {0,qmaClockMiddle T t,Fin.last (T+1)} := by
    intro b hb
    simpa only [Finset.mem_insert,Finset.mem_singleton] using
      qmaClockAnchorIndex_fiber T hT t b (Finset.mem_filter.mp hb).2
  apply (Finset.card_le_card hs).trans
  have h1 := Finset.card_insert_le (0 : Fin (T+2)) {qmaClockMiddle T t,Fin.last (T+1)}
  have h2 := Finset.card_insert_le (qmaClockMiddle T t) {Fin.last (T+1)}
  simp only [Finset.card_singleton] at h2
  omega

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTimeGrouping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal finite time grouping permutes the interaction list without duplicating terms. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

variable {α : Type*} [DecidableEq α]

def qmaGroupByTime (T : ℕ) (time : α → Fin T) (xs : List α) : List α :=
  (List.ofFn (fun t : Fin T => t)).flatMap (fun t => xs.filter (fun a => decide (time a = t)))

theorem qmaGroupByTime_count (T : ℕ) (time : α → Fin T) (xs : List α) (a : α) :
    (qmaGroupByTime T time xs).count a = xs.count a := by
  have hf (t : Fin T) : (xs.filter (fun b => decide (time b = t))).count a =
      if time a = t then xs.count a else 0 := by
    by_cases h : time a = t
    · simp only [h,ite_true, if_true]
      apply List.count_filter
      simp [h]
    · simp only [h,ite_false, if_false]
      apply List.count_eq_zero.mpr
      intro ha
      exact h (of_decide_eq_true (List.mem_filter.mp ha).2)
  simp only [qmaGroupByTime,List.count_flatMap,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  simp_rw [hf]
  simp

theorem qmaGroupByTime_perm (T : ℕ) (time : α → Fin T) (xs : List α) :
    (qmaGroupByTime T time xs).Perm xs :=
  List.perm_iff_count.mpr (qmaGroupByTime_count T time xs)

theorem qmaGroupByTime_length (T : ℕ) (time : α → Fin T) (xs : List α) :
    (qmaGroupByTime T time xs).length = xs.length :=
  (qmaGroupByTime_perm T time xs).length_eq

theorem qmaGroupByTime_nodup (T : ℕ) (time : α → Fin T) (xs : List α) (hx : xs.Nodup) :
    (qmaGroupByTime T time xs).Nodup :=
  (qmaGroupByTime_perm T time xs).nodup_iff.mpr hx

omit [DecidableEq α] in
theorem qmaGroupByTime_sorted (T : ℕ) (time : α → Fin T) (xs : List α) :
    (qmaGroupByTime T time xs).Pairwise (fun a b => time a ≤ time b) := by
  unfold qmaGroupByTime
  apply List.pairwise_flatMap.mpr
  constructor
  · intro t _
    apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    have ha' := of_decide_eq_true (List.mem_filter.mp ha).2
    have hb' := of_decide_eq_true (List.mem_filter.mp hb).2
    exact le_of_eq (ha'.trans hb'.symm)
  · apply List.pairwise_ofFn.mpr
    intro i j hij a ha b hb
    have ha' := of_decide_eq_true (List.mem_filter.mp ha).2
    have hb' := of_decide_eq_true (List.mem_filter.mp hb).2
    simpa only [ha',hb'] using le_of_lt hij

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTermTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assign every actual history term to its clock time and enumerate by time. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaBoundedClockTime (T : ℕ) (hT : 0 < T) (n : ℕ) : Fin T :=
  ⟨min n (T-1),by omega⟩

theorem qmaBoundedClockTime_eq (T : ℕ) (hT : 0 < T) (n : Fin T) :
    qmaBoundedClockTime T hT n.val = n := by
  apply Fin.ext
  simp only [qmaBoundedClockTime]
  exact min_eq_left (by omega)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSortedTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coverage at every clock time bounds jumps in the ordered interaction list. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

variable {α : Type*}

theorem qmaSortedTime_step {T : ℕ} (time : α → Fin T) (xs : List α)
    (hs : xs.Pairwise (fun a b => time a ≤ time b))
    (hc : ∀ t : Fin T, ∃ a ∈ xs, time a = t)
    (i j : Fin xs.length) (hj : j.val = i.val+1) :
    (time xs[j.val]).val ≤ (time xs[i.val]).val+1 := by
  by_contra hn
  have hgap : (time xs[i.val]).val+1 < (time xs[j.val]).val := by omega
  let t : Fin T := ⟨(time xs[i.val]).val+1,lt_trans hgap (time xs[j.val]).isLt⟩
  obtain ⟨a,ha,hat⟩ := hc t
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp ha
  have hk' : xs[k.val] = a := hk
  by_cases hki : k.val ≤ i.val
  · have hle : time xs[k.val] ≤ time xs[i.val] := by
      rcases lt_or_eq_of_le hki with hl | he
      · exact List.pairwise_iff_getElem.1 hs _ _ k.isLt i.isLt hl
      · simp only [he,le_refl]
    rw [hk',hat] at hle
    change (time xs[i.val]).val+1 ≤ (time xs[i.val]).val at hle
    omega
  · have hjk : j.val ≤ k.val := by omega
    have hle : time xs[j.val] ≤ time xs[k.val] := by
      rcases lt_or_eq_of_le hjk with hl | he
      · exact List.pairwise_iff_getElem.1 hs _ _ j.isLt k.isLt hl
      · simp only [he,le_refl]
    rw [hk',hat] at hle
    change (time xs[j.val]).val ≤ (time xs[i.val]).val+1 at hle
    omega

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTimeCongestion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At most eight actual interaction terms are assigned to any clock time. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaSumFilter_card {α β : Type*} [Fintype α] [Fintype β]
    (p : α ⊕ β → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card =
      (Finset.univ.filter (fun a => p (.inl a))).card+
      (Finset.univ.filter (fun b => p (.inr b))).card := by
  simp only [Finset.card_filter,Fintype.sum_sum_type]

theorem qmaBoundedClockTime_fiber_card (T : ℕ) (hT : 0 < T) (t : Fin T) :
    (Finset.univ.filter (fun i : Fin (T+1) => qmaBoundedClockTime T hT i.val = t)).card ≤ 2 := by
  have hs : Finset.univ.filter (fun i : Fin (T+1) => qmaBoundedClockTime T hT i.val = t) ⊆
      {t.castSucc,Fin.last T} := by
    intro i hi
    have hv := congrArg Fin.val (Finset.mem_filter.mp hi).2
    change min i.val (T-1) = t.val at hv
    have hit := i.isLt
    have htt := t.isLt
    have he : i.val = t.val ∨ i.val = T := by omega
    simpa only [Finset.mem_insert,Finset.mem_singleton] using
      he.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
  have hp := Finset.card_insert_le t.castSucc {Fin.last T}
  rw [Finset.card_singleton] at hp
  exact (Finset.card_le_card hs).trans hp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSparseEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The last physical gate sits immediately above the output qubit. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaGridQubit_last (rows width : ℕ) :
    qmaGridQubit rows width (Fin.last rows) (Fin.last width) =
      Fin.last (qmaGridWork rows width) := by
  apply Fin.ext
  simp only [qmaGridQubit,Fin.val_last,qmaGridWork]
  omega

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialClockTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Clock faults and endpoint pins are close to their assigned history time. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaBoundedClockTime_pair (T : ℕ) (hT : 0 < T) (i : Fin (T+1)) :
    (qmaBoundedClockTime T hT i.val).val ≤ i.val ∧
      i.val+1 ≤ (qmaBoundedClockTime T hT i.val).val+2 := by
  dsimp only [qmaBoundedClockTime]
  omega

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridNeighbors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Neighboring-cell geometry gives a constant interaction-degree bound. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaLineNeighbors {n : ℕ} (p : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun q => q.val ≤ p.val+1 ∧ p.val ≤ q.val+1)

theorem qmaLineNeighbors_card {n : ℕ} (p : Fin n) : (qmaLineNeighbors p).card ≤ 3 := by
  have hm : (qmaLineNeighbors p).card ≤ (Finset.Icc (p.val-1) (p.val+1)).card := by
    apply Finset.card_le_card_of_injOn Fin.val
    · intro q hq
      have h := (Finset.mem_filter.mp hq).2
      simp only [Finset.mem_coe,Finset.mem_Icc]
      omega
    · intro q _ r _ h
      exact Fin.ext h
  rw [Nat.card_Icc] at hm
  omega

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision preserves the grid and bounded density with explicit constant factors. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaProdFilter_card {α : Type*} [Fintype α] (n : ℕ) (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun q : α × Fin n => p q.1)).card =
      n*(Finset.univ.filter p).card := by
  have he : (Finset.univ.filter (fun q : α × Fin n => p q.1)) =
      (Finset.univ.filter p) ×ˢ (Finset.univ : Finset (Fin n)) := by
    ext q
    simp
  rw [he,Finset.card_product]
  simp only [Finset.card_univ,Fintype.card_fin,Nat.mul_comm]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumYYFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A YY term is a product of commuting real XZ and ZX involutions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaTwoPauliWord (i j : ι) (a b : Fin 4) : ι → Fin 4 :=
  fun k => if k = i then a else if k = j then b else 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliSingle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Pauli words for the mediator flip and occupation matrices. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaSinglePauliWord (i : ι) (a : Fin 4) : ι → Fin 4 := fun k => if k = i then a else 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumXZSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit X/Z Pauli output for subdivision, including its occupation term. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def qmaXZSubdivisionWord (a b : ι → Fin 4) (e : κ) : Fin 4 → (ι ⊕ κ → Fin 4) :=
  ![fun _ => 0, Sum.elim (fun _ => 0) (qmaSinglePauliWord e 3),
    Sum.elim a (qmaSinglePauliWord e 1), Sum.elim b (qmaSinglePauliWord e 1)]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumXZFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite X/Z word families with their actual normalized ground energy. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

structure QMAXZModel where
  Q : Type
  Term : Type
  [qFinite : Fintype Q]
  [qDecidable : DecidableEq Q]
  [termFinite : Fintype Term]
  word : Term → Q → Fin 4
  coefficient : Term → ℝ
  noY : ∀ e i, word e i ≠ 2
  card : ∀ e, (qmaPauliSupport (word e)).card ≤ 2

attribute [instance] QMAXZModel.qFinite QMAXZModel.qDecidable QMAXZModel.termFinite

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCircuitCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual parsing of the verifier's prefix circuit encoding. Register sizes
are clipped to supplied unary bounds before later finite enumerations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram

def sumView {α β : Type} (x : (α ⊕ β) × List Bool) :
    (α × List Bool) ⊕ (β × List Bool) :=
  match x.1 with
  | .inl a => .inl (a,x.2)
  | .inr b => .inr (b,x.2)

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTensorMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite tensor matrices used to place the proved four-spin code at every site. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical ComplexOrder
variable {Q σ τ υ : Type*} [Fintype Q] [DecidableEq Q] [Fintype σ] [Fintype τ] [Fintype υ]

def qmaTensorMatrix (A : Q → Matrix σ τ ℂ) : Matrix (Q → σ) (Q → τ) ℂ :=
  fun s t => ∏ i, A i (s i) (t i)

variable [DecidableEq σ]

def qmaSiteMatrix (i : Q) (A : Matrix σ σ ℂ) : Matrix (Q → σ) (Q → σ) ℂ :=
  qmaTensorMatrix (fun j => if j = i then A else 1)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTensorPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-block tensor placements and their exact algebra. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {Q σ : Type*} [Fintype Q] [DecidableEq Q] [Fintype σ] [DecidableEq σ]

def qmaPairMatrix (i j : Q) (A B : Matrix σ σ ℂ) : Matrix (Q → σ) (Q → σ) ℂ :=
  qmaTensorMatrix (fun k => if k = i then A else if k = j then B else 1)

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

def qmaFourAxis (a : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := if a = 0 then pauliX else pauliZ

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

def qmaFourEdgeLeft (e : Fin 6) : Fin 4 := ![0,0,0,1,1,2] e
def qmaFourEdgeRight (e : Fin 6) : Fin 4 := ![1,2,3,2,3,3] e

theorem qmaFourEdge_distinct (e : Fin 6) : qmaFourEdgeLeft e ≠ qmaFourEdgeRight e := by
  fin_cases e <;> decide

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

def qmaFieldEdgeRight (k : Fin 3) : Fin 4 := ![3,2,1] k

theorem qmaFieldEdgeRight_ne (k : Fin 3) : (0:Fin 4) ≠ qmaFieldEdgeRight k := by
  fin_cases k <;> decide

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumXZTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit scalar, one-site and two-site terms for the X/Z circuit family. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaXZLabel (a : Fin 2) : Fin 4 := if a = 0 then 1 else 3

inductive QMAXZTerm (n : ℕ) where
  | scalar
  | field (i : Fin n) (a : Fin 2)
  | pair (i j : Fin n) (hij : i ≠ j) (a b : Fin 2)

def QMAXZTerm.word {n : ℕ} : QMAXZTerm n → Fin n → Fin 4
  | .scalar => fun _ => 0
  | .field i a => fun k => if k = i then qmaXZLabel a else 0
  | .pair i j _ a b => fun k => if k = i then qmaXZLabel a else if k = j then qmaXZLabel b else 0

def QMAXZTerm.matrix {n : ℕ} : QMAXZTerm n → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ
  | .scalar => 1
  | .field i a => qmaSiteMatrix i (qmaFourAxis a)
  | .pair i j _ a b => qmaPairMatrix i j (qmaFourAxis a) (qmaFourAxis b)

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

structure QMAXZPair (n : ℕ) where
  left : Fin n
  right : Fin n
  distinct : left ≠ right
  axisLeft : Fin 2
  axisRight : Fin 2

structure QMAXZField (n : ℕ) where
  site : Fin n
  axis : Fin 2

def QMAXZTerm.IsPair {n : ℕ} : QMAXZTerm n → Prop
  | .pair .. => True
  | _ => False

def QMAXZTerm.IsField {n : ℕ} : QMAXZTerm n → Prop
  | .field .. => True
  | _ => False

def QMAXZTerm.IsScalar {n : ℕ} : QMAXZTerm n → Prop
  | .scalar => True
  | _ => False

def QMAXZTerm.asPair {n : ℕ} (t : QMAXZTerm n) (h : t.IsPair) : QMAXZPair n := by
  cases t with
  | scalar => exact h.elim
  | field => exact h.elim
  | pair i j hij a b => exact ⟨i,j,hij,a,b⟩

def QMAXZTerm.asField {n : ℕ} (t : QMAXZTerm n) (h : t.IsField) : QMAXZField n := by
  cases t with
  | scalar => exact h.elim
  | field i a => exact ⟨i,a⟩
  | pair => exact h.elim

variable {n : ℕ} {κ : Type*} [Fintype κ]

abbrev QMAXZPairIndex (t : κ → QMAXZTerm n) := {e // (t e).IsPair}
abbrev QMAXZFieldIndex (t : κ → QMAXZTerm n) := {e // (t e).IsField}
abbrev QMAXZScalarIndex (t : κ → QMAXZTerm n) := {e // (t e).IsScalar}

def qmaXZPairData (t : κ → QMAXZTerm n) (e : QMAXZPairIndex t) : QMAXZPair n :=
  (t e.val).asPair e.property

def qmaXZFieldData (t : κ → QMAXZTerm n) (e : QMAXZFieldIndex t) : QMAXZField n :=
  (t e.val).asField e.property

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAxisSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational sampling of the fixed algebraic constants in the four-spin encoding. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open scoped Classical

def inverseScale (a : Fin 2) : ℝ := if a = 0 then Real.sqrt 3/384 else 3/4

end ContinuumCoulomb.QuantumAxisSample

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

def qmaXZInputSize (J : κ → ℝ) : ℝ := Fintype.card κ+∑ e, |J e|

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCountertermSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The counterterms use only rational arithmetic and the fixed inverse-scale sample. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open scoped Classical

def shift (a : Fin 2) (p : Bool) : ℚ := if a = 0 then 400 else if p then 8/3 else 4/3
def polarity (t : ℚ) : ℚ := if t ≤ 0 then 1 else -1

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOffsetSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Error bounds for the sampled counterterm fields and their scalar shifts. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

def shiftValue (a : Fin 2) (t : ℚ) : ℚ := if a = 0 then 0 else t/2

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumExchangeSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certified rational values for every edge of the actual physical exchange family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped Classical BigOperators

def stencil (a : Fin 2) (s : Bool) : Fin 4 → ℚ :=
  if a = 0 then if s then ![11,-1,-13,3] else ![11,-1,3,-13]
  else if s then ![1,-1,0,0] else ![1,1,0,0]

variable {n : ℕ} {κ τ : Type*}

def weightErrorBudget (r B : ℝ) : ℝ := 1568*|r| *(1+B)+26064*B

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumExchangeSampleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal evaluation of each cross-block physical exchange coefficient. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram

abbrev CrossInput := (ℕ × ℚ) × ℚ

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Raw, rational finite-list instructions for the four-spin compiler. -/

namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample ExactQuantumFactoring.BitStackProgram

abbrev Raw := (Bool × Bool) × ((ℕ × ℕ) × ((Bool × Bool) × ℚ))

def axis (a : Bool) : Fin 2 := if a then 0 else 1

def pack {n : ℕ} (t : QMAXZTerm n) (J : ℚ) : Raw :=
  match t with
  | .scalar => ((false,false),((0,0),((false,false),J)))
  | .field i a => ((false,true),((i,0),((decide (a = 0),false),J)))
  | .pair i j _ a b => ((true,false),((i,j),((decide (a = 0),decide (b = 0)),J)))

theorem axis_pack (a : Fin 2) : axis (decide (a = 0)) = a := by
  fin_cases a <;> rfl

abbrev Environment := ℕ × ℚ
abbrev Input := Environment × Raw

end ContinuumCoulomb.QuantumRawExchange

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
open QuantumAxisSample ExactQuantumFactoring.BitStackProgram

theorem fold_append {α : Type} (xs : List (List α)) (ys : List α) :
    xs.foldl (fun ys x => ys++x) ys = ys++xs.flatten := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons,ih,List.flatten_cons,List.append_assoc]

abbrev FamilyInput := Environment × List Raw

def zeroRaw : Raw := ((false,false),((0,0),((false,false),0)))

abbrev PenaltyInput := ℕ × ℚ

abbrev FullInput := ℕ × FamilyInput

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAdjacentProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The recursive adjacent-CNOT construction is a literal finite prefix,
one central gate, and its reversed prefix. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram

abbrev AdjacentInput := ℕ × (ℕ × Bool)

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAlgebraicScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar arithmetic for the H,T,CNOT history compiler.  A real
scalar is a+b/sqrt(2); a complex scalar consists of two such pairs.  The
representation is rational data throughout, including multiplication. -/

namespace ContinuumCoulomb.QuantumAlgebraicScalar

abbrev RealScalar := ℚ × ℚ
abbrev Scalar := RealScalar × RealScalar

def realRat (a : ℚ) : RealScalar := (a,0)
def realAdd (x y : RealScalar) : RealScalar := (x.1+y.1,x.2+y.2)
def realNeg (x : RealScalar) : RealScalar := (-x.1,-x.2)
def realSub (x y : RealScalar) : RealScalar := realAdd x (realNeg y)
def realMul (x y : RealScalar) : RealScalar :=
  (x.1*y.1+x.2*y.2/2,x.1*y.2+x.2*y.1)
def rat (a : ℚ) : Scalar := (realRat a,realRat 0)
def add (x y : Scalar) : Scalar := (realAdd x.1 y.1,realAdd x.2 y.2)
def neg (x : Scalar) : Scalar := (realNeg x.1,realNeg x.2)
def sub (x y : Scalar) : Scalar := add x (neg y)
def mul (x y : Scalar) : Scalar :=
  (realSub (realMul x.1 y.1) (realMul x.2 y.2),
    realAdd (realMul x.1 y.2) (realMul x.2 y.1))
def conj (x : Scalar) : Scalar := (x.1,realNeg x.2)
def sqrtHalf : Scalar := ((0,1),(0,0))
def imaginary : Scalar := ((0,0),(1,0))
def realPart (x : Scalar) : Scalar := (x.1,realRat 0)
def imagPart (x : Scalar) : Scalar := (x.2,realRat 0)

noncomputable def realValue (x : RealScalar) : ℝ :=
  (x.1:ℝ)+(x.2:ℝ)*Real.sqrt (1/2:ℝ)
noncomputable def value (x : Scalar) : ℂ :=
  (realValue x.1:ℂ)+(realValue x.2:ℂ)*Complex.I

@[simp] theorem realValue_rat (a : ℚ) : realValue (realRat a) = (a:ℝ) := by
  simp [realValue,realRat]

@[simp] theorem realValue_add (x y : RealScalar) :
    realValue (realAdd x y) = realValue x+realValue y := by
  simp only [realValue,realAdd,Rat.cast_add]
  ring

@[simp] theorem realValue_neg (x : RealScalar) : realValue (realNeg x) = -realValue x := by
  simp only [realValue,realNeg,Rat.cast_neg]
  ring

@[simp] theorem realValue_sub (x y : RealScalar) :
    realValue (realSub x y) = realValue x-realValue y := by
  simp [realSub,sub_eq_add_neg]

@[simp] theorem realValue_mul (x y : RealScalar) :
    realValue (realMul x y) = realValue x*realValue y := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)
  simp only [realValue,realMul,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat]
  linear_combination -(x.2:ℝ)*(y.2:ℝ)*hs

@[simp] theorem value_re (x : Scalar) : (value x).re = realValue x.1 := by
  simp [value]

@[simp] theorem value_im (x : Scalar) : (value x).im = realValue x.2 := by
  simp [value]

@[simp] theorem value_rat (a : ℚ) : value (rat a) = (a:ℂ) := by
  simp [value,rat]

@[simp] theorem value_add (x y : Scalar) : value (add x y) = value x+value y := by
  apply Complex.ext <;> simp [add]

@[simp] theorem value_neg (x : Scalar) : value (neg x) = -value x := by
  apply Complex.ext <;> simp [neg]

@[simp] theorem value_sub (x y : Scalar) : value (sub x y) = value x-value y := by
  simp [sub,sub_eq_add_neg]

@[simp] theorem value_mul (x y : Scalar) : value (mul x y) = value x*value y := by
  apply Complex.ext <;> simp [mul,Complex.mul_re,Complex.mul_im]

@[simp] theorem value_conj (x : Scalar) : value (conj x) = star (value x) := by
  apply Complex.ext <;> simp [conj]

@[simp] theorem value_sqrtHalf : value sqrtHalf = bellScale := by
  simp [value,sqrtHalf,realValue,bellScale]

@[simp] theorem value_imaginary : value imaginary = Complex.I := by
  simp [value,imaginary,realValue]

@[simp] theorem value_realPart (x : Scalar) : value (realPart x) = ((value x).re:ℂ) := by
  simp [value,realPart]

@[simp] theorem value_imagPart (x : Scalar) : value (imagPart x) = ((value x).im:ℂ) := by
  simp [value,imagPart]

def sum : List Scalar → Scalar
  | [] => rat 0
  | x::xs => add x (sum xs)

def product : List Scalar → Scalar
  | [] => rat 1
  | x::xs => mul x (product xs)

@[simp] theorem value_sum (xs : List Scalar) : value (sum xs) = (xs.map value).sum := by
  induction xs with
  | nil => simp [sum]
  | cons x xs ih => simp [sum,ih]

@[simp] theorem value_product (xs : List Scalar) : value (product xs) = (xs.map value).prod := by
  induction xs with
  | nil => simp [product]
  | cons x xs ih => simp [product,ih]

end ContinuumCoulomb.QuantumAlgebraicScalar

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAlgebraicHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational coefficient-height bounds for the fixed history expressions.
These bounds provide a polynomial precision budget before real evaluation. -/

namespace ContinuumCoulomb.QuantumAlgebraicScalar
open scoped BigOperators

def realHeight (x : RealScalar) : ℚ := |x.1|+|x.2|
def height (x : Scalar) : ℚ := realHeight x.1+realHeight x.2

@[simp] theorem realHeight_rat (a : ℚ) : realHeight (realRat a) = |a| := by
  simp [realHeight,realRat]

@[simp] theorem realHeight_neg (x : RealScalar) : realHeight (realNeg x) = realHeight x := by
  simp [realHeight,realNeg]

@[simp] theorem height_rat (a : ℚ) : height (rat a) = |a| := by
  simp [height,rat]

@[simp] theorem height_neg (x : Scalar) : height (neg x) = height x := by
  simp [height,neg]

@[simp] theorem height_conj (x : Scalar) : height (conj x) = height x := by
  simp [height,conj]

@[simp] theorem height_sqrtHalf : height sqrtHalf = 1 := by
  norm_num [height,realHeight,sqrtHalf]

@[simp] theorem height_imaginary : height imaginary = 1 := by
  norm_num [height,realHeight,imaginary]

end ContinuumCoulomb.QuantumAlgebraicScalar

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFixedPauli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-arity Pauli traces evaluated entirely in rational registers.
The interpretation is the actual complex Pauli coefficient, not an
assumed list of Hamiltonian coefficients. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFixedPauli
open QuantumAlgebraicScalar Matrix
open scoped BigOperators Classical

def enumerate (α : Type) [Fintype α] : List α :=
  List.ofFn (Fintype.equivFin α).symm

def finiteSum {α : Type} [Fintype α] (f : α → Scalar) : Scalar :=
  QuantumAlgebraicScalar.sum ((enumerate α).map f)

def finiteProduct {α : Type} [Fintype α] (f : α → Scalar) : Scalar :=
  QuantumAlgebraicScalar.product ((enumerate α).map f)

def pauli (μ : Fin 4) : Matrix (Fin 2) (Fin 2) Scalar :=
  ![!![rat 1,rat 0;rat 0,rat 1],
    !![rat 0,rat 1;rat 1,rat 0],
    !![rat 0,neg imaginary;imaginary,rat 0],
    !![rat 1,rat 0;rat 0,rat (-1)]] μ

def word {ι : Type} [Fintype ι] (w : ι → Fin 4) (s t : ι → Fin 2) : Scalar :=
  finiteProduct (fun i => pauli (w i) (s i) (t i))

def coefficient {ι : Type} [Fintype ι] (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (w : ι → Fin 4) : Scalar :=
  mul (rat ((2:ℚ)^Fintype.card ι)⁻¹)
    (finiteSum (fun s => finiteSum (fun t => mul (A s t) (word w t s))))

def realCoefficient {ι : Type} [Fintype ι]
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) (w : ι → Fin 4) : RealScalar :=
  (coefficient A w).1

end ContinuumCoulomb.QuantumFixedPauli

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAlgebraicHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual ordered history cores have exact four-rational entries.  The
propagation Gram is formed on its at-most-five-site core; the construction
does not sum over spectator configurations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

def denote {α β : Type} (A : Matrix α β Scalar) : Matrix α β ℂ :=
  fun s t => value (A s t)

def matMul {α β γ : Type} [Fintype β]
    (A : Matrix α β Scalar) (B : Matrix β γ Scalar) : Matrix α γ Scalar :=
  fun s t => finiteSum (fun u => mul (A s u) (B u t))

def adjoint {α β : Type} (A : Matrix α β Scalar) : Matrix β α Scalar :=
  fun s t => conj (A t s)

def hadamard (s t : Fin 2) : Scalar :=
  mul sqrtHalf (rat (if s = 1 ∧ t = 1 then -1 else 1))

def phaseT (s t : Fin 2) : Scalar :=
  if s = t then (if s = 0 then rat 1 else mul sqrtHalf (add (rat 1) imaginary)) else rat 0

def identity {α : Type} [DecidableEq α] (s t : α) : Scalar := rat (if s = t then 1 else 0)

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBitTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer a bit-coded word between the verifier machine and the Boolean
prefix tapes. Only the bit register is added to the finite control. -/

namespace ContinuumCoulomb.QuantumBitTransfer
open Turing

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

def loop (src dst : K) (read : Γ src → Bool) (write : Bool → Γ dst)
    (label : Λ) (exit : Option Λ) : TM2.Stmt Γ Λ (σ × Option Bool) :=
  .pop src (fun s h => (s.1,h.map read))
    (.branch (fun s => s.2.isSome)
      (.push dst (fun s => write (s.2.getD false)) (.goto fun _ => label))
      (match exit with | none => .halt | some l => .goto fun _ => l))

end ContinuumCoulomb.QuantumBitTransfer

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumManhattanSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact support of the two-segment lattice route. -/

namespace ContinuumCoulomb

def qmaBetween (a b x : ℕ) : Prop := min a b ≤ x ∧ x ≤ max a b

def qmaManhattanSupport (p q z : ℕ × ℕ) : Prop :=
  (z.2 = p.2 ∧ qmaBetween p.1 q.1 z.1) ∨
    (z.1 = q.1 ∧ qmaBetween p.2 q.2 z.2)

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedFanout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint arms offset from all global grid lines, with a one-step terminal join. -/

namespace ContinuumCoulomb

def qmaBufferedPort (c : Fin 3 → ℕ) (a : Fin 3) : ℕ := 8*(c a+3)
def qmaBufferedOffset (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) : ℕ :=
  if side a then qmaBufferedPort c a+1 else qmaBufferedPort c a-1

theorem qmaBufferedOffset_bounds (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) :
    qmaBufferedPort c a ≤ qmaBufferedOffset c side a+1 ∧
      qmaBufferedOffset c side a ≤ qmaBufferedPort c a+1 := by
  unfold qmaBufferedOffset
  split_ifs <;> omega

theorem qmaBufferedOffset_not_grid (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) (u : ℕ) :
    qmaBufferedOffset c side a ≠ 8*u := by
  unfold qmaBufferedOffset qmaBufferedPort
  split_ifs <;> omega

def qmaBufferedFanoutSupport (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) (p : ℕ × ℕ) : Prop :=
  if a = 0 then
    (p.2 = 17 ∧ 17 ≤ p.1 ∧ p.1 ≤ qmaBufferedOffset c side 0) ∨
    (p.1 = qmaBufferedOffset c side 0 ∧ 17 ≤ p.2 ∧ p.2 ≤ qmaBufferedPort c 0) ∨
    (p.2 = qmaBufferedPort c 0 ∧ qmaBetween (qmaBufferedOffset c side 0) (qmaBufferedPort c 0) p.1)
  else if a = 1 then
    (p.1 = 17 ∧ 17 ≤ p.2 ∧ p.2 ≤ qmaBufferedOffset c side 1) ∨
    (p.2 = qmaBufferedOffset c side 1 ∧ 17 ≤ p.1 ∧ p.1 ≤ qmaBufferedPort c 1) ∨
    (p.1 = qmaBufferedPort c 1 ∧ qmaBetween (qmaBufferedOffset c side 1) (qmaBufferedPort c 1) p.2)
  else
    (p.2 = 17 ∧ 9 ≤ p.1 ∧ p.1 ≤ 17) ∨
    (p.1 = 9 ∧ 17 ≤ p.2 ∧ p.2 ≤ 8*(c 2+4)+1) ∨
    (p.2 = 8*(c 2+4)+1 ∧ 9 ≤ p.1 ∧ p.1 ≤ qmaBufferedOffset c side 2) ∨
    (p.1 = qmaBufferedOffset c side 2 ∧ qmaBufferedPort c 2 ≤ p.2 ∧ p.2 ≤ 8*(c 2+4)+1) ∨
    (p.2 = qmaBufferedPort c 2 ∧ qmaBetween (qmaBufferedOffset c side 2) (qmaBufferedPort c 2) p.1)

theorem qmaBufferedFanout_only_center (c : Fin 3 → ℕ) (h01 : c 0 < c 1) (h12 : c 1 < c 2)
    (side : Fin 3 → Bool) {a b : Fin 3} (hab : a ≠ b) {p : ℕ × ℕ}
    (ha : qmaBufferedFanoutSupport c side a p) (hb : qmaBufferedFanoutSupport c side b p) : p = (17,17) := by
  have h0 := qmaBufferedOffset_bounds c side 0
  have h1 := qmaBufferedOffset_bounds c side 1
  have h2 := qmaBufferedOffset_bounds c side 2
  dsimp [qmaBufferedPort] at h0 h1 h2
  rcases p with ⟨x,y⟩
  fin_cases a <;> fin_cases b <;>
    simp [qmaBufferedFanoutSupport,qmaBufferedPort,qmaBetween] at ha hb hab ⊢ <;> omega

theorem qmaBufferedFanout_grid_point (c : Fin 3 → ℕ) (side : Fin 3 → Bool)
    (a : Fin 3) (u v : ℕ) (h : qmaBufferedFanoutSupport c side a (8*u,8*v)) :
    (8*u,8*v) = (qmaBufferedPort c a,qmaBufferedPort c a) := by
  have h0 := qmaBufferedOffset_bounds c side 0
  have h1 := qmaBufferedOffset_bounds c side 1
  have h2 := qmaBufferedOffset_bounds c side 2
  have h0x := qmaBufferedOffset_not_grid c side 0 u
  have h1y := qmaBufferedOffset_not_grid c side 1 v
  have h2x := qmaBufferedOffset_not_grid c side 2 u
  dsimp [qmaBufferedPort] at h0 h1 h2 ⊢
  fin_cases a <;> simp [qmaBufferedFanoutSupport,qmaBufferedPort,qmaBetween] at h ⊢ <;> omega

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedDogleg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two direct buffered endpoint arms, including their one-step joins. -/

namespace ContinuumCoulomb

def qmaBufferedDoglegLength (u v : ℕ) : ℕ := (v-17)+(u-17)+1

def qmaBufferedDoglegPoint (u v k : ℕ) : ℕ × ℕ :=
  if k ≤ v-17 then (17+k,17)
  else if k ≤ (v-17)+(u-17) then (v,17+(k-(v-17)))
  else (u,u)

def qmaBufferedDoglegSupport (u v : ℕ) (p : ℕ × ℕ) : Prop :=
  (p.2 = 17 ∧ 17 ≤ p.1 ∧ p.1 ≤ v) ∨
  (p.1 = v ∧ 17 ≤ p.2 ∧ p.2 ≤ u) ∨
  (p.2 = u ∧ qmaBetween v u p.1)

theorem qmaBufferedDogleg_zero (u v : ℕ) : qmaBufferedDoglegPoint u v 0 = (17,17) := by
  simp [qmaBufferedDoglegPoint]

theorem qmaBufferedDogleg_support {u v : ℕ} (hu : 24 ≤ u) (hv : 23 ≤ v) (k : ℕ) :
    qmaBufferedDoglegSupport u v (qmaBufferedDoglegPoint u v k) := by
  unfold qmaBufferedDoglegPoint
  split_ifs <;> simp [qmaBufferedDoglegSupport,qmaBetween] <;> omega

theorem qmaBufferedDogleg_step {u v : ℕ} (hu : 24 ≤ u) (hv : 23 ≤ v)
    (hclose : u ≤ v+1 ∧ v ≤ u+1) (hne : u ≠ v) (k : ℕ)
    (hk : k < qmaBufferedDoglegLength u v) :
    Nat.dist (qmaBufferedDoglegPoint u v k).1 (qmaBufferedDoglegPoint u v (k+1)).1+
      Nat.dist (qmaBufferedDoglegPoint u v k).2 (qmaBufferedDoglegPoint u v (k+1)).2 = 1 := by
  unfold qmaBufferedDoglegPoint qmaBufferedDoglegLength at *
  split_ifs <;> simp_all [Nat.dist] <;> omega

theorem qmaBufferedDogleg_length_bound {u v U : ℕ} (hu : u ≤ U) (hv : v ≤ u+1) :
    qmaBufferedDoglegLength u v ≤ 2*U+2 := by
  unfold qmaBufferedDoglegLength
  omega

theorem qmaBufferedFanout_direct_support (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (k : ℕ) :
    qmaBufferedFanoutSupport c side 0
      (qmaBufferedDoglegPoint (qmaBufferedPort c 0) (qmaBufferedOffset c side 0) k) := by
  have hb := qmaBufferedOffset_bounds c side 0
  have hu : 24 ≤ qmaBufferedPort c 0 := by unfold qmaBufferedPort; omega
  have hv : 23 ≤ qmaBufferedOffset c side 0 := by omega
  exact qmaBufferedDogleg_support hu hv k

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedDetour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit western detour for the third buffered endpoint arm. -/

namespace ContinuumCoulomb

def qmaBufferedDetourPoint (u v k : ℕ) : ℕ × ℕ :=
  if k ≤ 8 then (17-k,17)
  else if k ≤ u then (9,k+9)
  else if k ≤ u+v-9 then (k-u+9,u+9)
  else if k ≤ u+v then (v,2*u+v-k)
  else (u,u)

def qmaBufferedDetourSupport (u v : ℕ) (p : ℕ × ℕ) : Prop :=
  (p.2 = 17 ∧ 9 ≤ p.1 ∧ p.1 ≤ 17) ∨
  (p.1 = 9 ∧ 17 ≤ p.2 ∧ p.2 ≤ u+9) ∨
  (p.2 = u+9 ∧ 9 ≤ p.1 ∧ p.1 ≤ v) ∨
  (p.1 = v ∧ u ≤ p.2 ∧ p.2 ≤ u+9) ∨
  (p.2 = u ∧ qmaBetween v u p.1)

theorem qmaBufferedDetour_zero (u v : ℕ) : qmaBufferedDetourPoint u v 0 = (17,17) := by
  simp [qmaBufferedDetourPoint]

theorem qmaBufferedDetour_support {u v : ℕ} (hu : 24 ≤ u) (hv : 23 ≤ v) (k : ℕ) :
    qmaBufferedDetourSupport u v (qmaBufferedDetourPoint u v k) := by
  unfold qmaBufferedDetourPoint
  split_ifs <;> simp [qmaBufferedDetourSupport,qmaBetween] <;> omega

theorem qmaBufferedDetour_step {u v : ℕ} (hu : 24 ≤ u) (hv : 23 ≤ v)
    (hclose : u ≤ v+1 ∧ v ≤ u+1) (hne : u ≠ v) (k : ℕ) (hk : k < u+v+1) :
    Nat.dist (qmaBufferedDetourPoint u v k).1 (qmaBufferedDetourPoint u v (k+1)).1+
      Nat.dist (qmaBufferedDetourPoint u v k).2 (qmaBufferedDetourPoint u v (k+1)).2 = 1 := by
  unfold qmaBufferedDetourPoint
  split_ifs <;> simp_all [Nat.dist] <;> omega

theorem qmaBufferedFanout_detour_support (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (k : ℕ) :
    qmaBufferedFanoutSupport c side 2
      (qmaBufferedDetourPoint (qmaBufferedPort c 2) (qmaBufferedOffset c side 2) k) := by
  have hb := qmaBufferedOffset_bounds c side 2
  have hu : 24 ≤ qmaBufferedPort c 2 := by unfold qmaBufferedPort; omega
  have hv : 23 ≤ qmaBufferedOffset c side 2 := by omega
  have hs := qmaBufferedDetour_support hu hv k
  have he : qmaBufferedPort c 2+9 = 8*(c 2+4)+1 := by unfold qmaBufferedPort; omega
  simpa [qmaBufferedDetourSupport,qmaBufferedFanoutSupport,he] using hs

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedArms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite-walk interface for all three buffered endpoint arms. -/

namespace ContinuumCoulomb

def qmaBufferedArmLength (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) : ℕ :=
  if a = 2 then qmaBufferedPort c a + qmaBufferedOffset c side a + 1
  else qmaBufferedDoglegLength (qmaBufferedPort c a) (qmaBufferedOffset c side a)

def qmaBufferedArmPoint (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) (k : ℕ) : ℕ × ℕ :=
  if a = 0 then qmaBufferedDoglegPoint (qmaBufferedPort c a) (qmaBufferedOffset c side a) k
  else if a = 1 then (qmaBufferedDoglegPoint (qmaBufferedPort c a) (qmaBufferedOffset c side a) k).swap
  else qmaBufferedDetourPoint (qmaBufferedPort c a) (qmaBufferedOffset c side a) k

theorem qmaBufferedOffset_ne (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) :
    qmaBufferedPort c a ≠ qmaBufferedOffset c side a := by
  unfold qmaBufferedOffset qmaBufferedPort
  split_ifs <;> omega

@[simp] theorem qmaBufferedArm_zero (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) :
    qmaBufferedArmPoint c side a 0 = (17,17) := by
  fin_cases a <;> simp [qmaBufferedArmPoint,qmaBufferedDogleg_zero,qmaBufferedDetour_zero]

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedArmProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal evaluation and enumeration of the three buffered endpoint arms.
The lane color is unary, as required by the polynomial geometric size bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumBufferedArmProgram
open ExactQuantumFactoring.BitStackProgram

def length (a : Fin 3) (color : ℕ) : ℕ :=
  if a = 2 then 16*color+48 else 16*color+14

end ContinuumCoulomb.QuantumBufferedArmProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFineRoute
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite lattice routes stay in the neighboring coarse cells of their endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaQuotient_bounds (p q x A : ℕ) (hl : min p q ≤ x) (hu : x ≤ max p q) :
    min (p/A) (q/A) ≤ x/A ∧ x/A ≤ max (p/A) (q/A) := by
  by_cases hpq : p ≤ q
  · have hd := Nat.div_le_div_right (c := A) hpq
    rw [min_eq_left hpq] at hl
    rw [max_eq_right hpq] at hu
    rw [min_eq_left hd,max_eq_right hd]
    exact ⟨Nat.div_le_div_right hl,Nat.div_le_div_right hu⟩
  · have hqp : q ≤ p := by omega
    have hd := Nat.div_le_div_right (c := A) hqp
    rw [min_eq_right hqp] at hl
    rw [max_eq_left hqp] at hu
    rw [min_eq_right hd,max_eq_left hd]
    exact ⟨Nat.div_le_div_right hl,Nat.div_le_div_right hu⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRouteLanes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct residue lanes separate parallel routes and keep crossings away from bends. -/

namespace ContinuumCoulomb

def qmaLanePoint {C : ℕ} (c : Fin C) (p : ℕ × ℕ) : ℕ × ℕ :=
  (C*p.1+c.val,C*p.2+c.val)

@[simp] theorem qmaLanePoint_row_mod {C : ℕ} (c : Fin C) (p : ℕ × ℕ) :
    (qmaLanePoint c p).1%C = c.val := by
  simp [qmaLanePoint,Nat.add_mod,Nat.mod_eq_of_lt c.isLt]

@[simp] theorem qmaLanePoint_col_mod {C : ℕ} (c : Fin C) (p : ℕ × ℕ) :
    (qmaLanePoint c p).2%C = c.val := by
  simp [qmaLanePoint,Nat.add_mod,Nat.mod_eq_of_lt c.isLt]

def qmaHorizontalLane {C : ℕ} (c : Fin C) (y : ℕ) (p : ℕ × ℕ) : Prop :=
  p.2 = C*y+c.val

def qmaVerticalLane {C : ℕ} (c : Fin C) (x : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 = C*x+c.val

theorem qmaHorizontalLane_color {C : ℕ} {c d : Fin C} {y z : ℕ} {p : ℕ × ℕ}
    (hc : qmaHorizontalLane c y p) (hd : qmaHorizontalLane d z p) : c = d := by
  apply Fin.ext
  have he : (C*y+c.val)%C = (C*z+d.val)%C := congrArg (fun x => x%C) (hc.symm.trans hd)
  simpa [Nat.add_mod,Nat.mod_eq_of_lt c.isLt,Nat.mod_eq_of_lt d.isLt] using he

theorem qmaVerticalLane_color {C : ℕ} {c d : Fin C} {x z : ℕ} {p : ℕ × ℕ}
    (hc : qmaVerticalLane c x p) (hd : qmaVerticalLane d z p) : c = d := by
  apply Fin.ext
  have he : (C*x+c.val)%C = (C*z+d.val)%C := congrArg (fun x => x%C) (hc.symm.trans hd)
  simpa [Nat.add_mod,Nat.mod_eq_of_lt c.isLt,Nat.mod_eq_of_lt d.isLt] using he

/-- A transverse crossing between distinct lanes cannot coincide with any lane vertex. -/
theorem qmaLane_crossing_not_vertex {C : ℕ} {c d : Fin C} (hcd : c ≠ d)
    {x y : ℕ} {p : ℕ × ℕ} (hh : qmaHorizontalLane c y p) (hv : qmaVerticalLane d x p)
    (e : Fin C) (q : ℕ × ℕ) : p ≠ qmaLanePoint e q := by
  intro he
  subst p
  have hc : c = e := qmaHorizontalLane_color hh (by rfl : qmaHorizontalLane e q.2 (qmaLanePoint e q))
  have hd : d = e := qmaVerticalLane_color hv (by rfl : qmaVerticalLane e q.1 (qmaLanePoint e q))
  exact hcd (hc.trans hd.symm)

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Buffered endpoint cells align with spaced lanes and are mutually disjoint. -/

namespace ContinuumCoulomb

def qmaBufferedCellPoint (C : ℕ) (p z : ℕ × ℕ) : ℕ × ℕ :=
  (8*(C+6)*p.1+z.1,8*(C+6)*p.2+z.2)

theorem qmaBufferedFanout_bounded (c : Fin 3 → ℕ) (h01 : c 0 < c 1) (h12 : c 1 < c 2)
    {C : ℕ} (hC : c 2 < C) (side : Fin 3 → Bool) (a : Fin 3) {z : ℕ × ℕ}
    (hz : qmaBufferedFanoutSupport c side a z) :
    0 < z.1 ∧ z.1 < 8*(C+6) ∧ 0 < z.2 ∧ z.2 < 8*(C+6) := by
  have h0 := qmaBufferedOffset_bounds c side 0
  have h1 := qmaBufferedOffset_bounds c side 1
  have h2 := qmaBufferedOffset_bounds c side 2
  dsimp [qmaBufferedPort] at h0 h1 h2
  fin_cases a <;> simp [qmaBufferedFanoutSupport,qmaBufferedPort,qmaBetween] at hz <;> omega

theorem qmaBufferedCellPoint_cell (C : ℕ) (p z : ℕ × ℕ)
    (hx : z.1 < 8*(C+6)) (hy : z.2 < 8*(C+6)) :
    ((qmaBufferedCellPoint C p z).1/(8*(C+6)),
      (qmaBufferedCellPoint C p z).2/(8*(C+6))) = p := by
  have hw : 0 < 8*(C+6) := by omega
  apply Prod.ext <;> dsimp [qmaBufferedCellPoint]
  · rw [Nat.add_comm,Nat.add_mul_div_left _ _ hw,Nat.div_eq_of_lt hx,zero_add]
  · rw [Nat.add_comm,Nat.add_mul_div_left _ _ hw,Nat.div_eq_of_lt hy,zero_add]

theorem qmaBufferedCellPoint_disjoint {C : ℕ} {p q x y : ℕ × ℕ} (hpq : p ≠ q)
    (hx : x.1 < 8*(C+6) ∧ x.2 < 8*(C+6))
    (hy : y.1 < 8*(C+6) ∧ y.2 < 8*(C+6)) :
    qmaBufferedCellPoint C p x ≠ qmaBufferedCellPoint C q y := by
  intro h
  have hd := congrArg (fun z : ℕ × ℕ => (z.1/(8*(C+6)),z.2/(8*(C+6)))) h
  rw [qmaBufferedCellPoint_cell C p x hx.1 hx.2,qmaBufferedCellPoint_cell C q y hy.1 hy.2] at hd
  exact hpq hd

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourSpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four-spin encoding preserves neighboring-cell geometry and constant density. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
variable {n rows width : ℕ} {κ τ : Type*} [Fintype κ] [Fintype τ]

theorem qmaProductFilter_card {α β : Type*} [Fintype α] [Fintype β]
    (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun q : α × β => p q.1)).card =
      Fintype.card β*(Finset.univ.filter p).card := by
  have he : (Finset.univ.filter (fun q : α × β => p q.1)) =
      (Finset.univ.filter p) ×ˢ (Finset.univ : Finset β) := by ext q; simp
  rw [he,Finset.card_product]
  simp only [Finset.card_univ,Nat.mul_comm]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLaneSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lane expansion preserves disjoint paths; different lanes meet only transversely. -/

namespace ContinuumCoulomb

def qmaLaneDown (C : ℕ) (z : ℕ × ℕ) : ℕ × ℕ := (z.1/C,z.2/C)

@[simp] theorem qmaLaneDown_point {C : ℕ} (c : Fin C) (p : ℕ × ℕ) :
    qmaLaneDown C (qmaLanePoint c p) = p := by
  have hC : 0 < C := (Nat.zero_le c.val).trans_lt c.isLt
  apply Prod.ext <;> dsimp [qmaLaneDown,qmaLanePoint]
  all_goals rw [Nat.add_comm,Nat.add_mul_div_left _ _ hC,Nat.div_eq_of_lt c.isLt,zero_add]

def qmaLaneSupport {C : ℕ} (c : Fin C) (p q z : ℕ × ℕ) : Prop :=
  qmaManhattanSupport (qmaLanePoint c p) (qmaLanePoint c q) z

theorem qmaLaneSupport_down {C : ℕ} (c : Fin C) {p q z : ℕ × ℕ}
    (hz : qmaLaneSupport c p q z) : qmaManhattanSupport p q (qmaLaneDown C z) := by
  have hdownp := qmaLaneDown_point c p
  have hdownq := qmaLaneDown_point c q
  rcases hz with ⟨hy,hx⟩ | ⟨hx,hy⟩
  · left
    refine ⟨?_,?_⟩
    · have h := congrArg (fun x => x/C) hy
      change (qmaLaneDown C z).2 = (qmaLaneDown C (qmaLanePoint c p)).2 at h
      rw [hdownp] at h
      exact h
    · have h := qmaQuotient_bounds _ _ _ C hx.1 hx.2
      change min ((qmaLaneDown C (qmaLanePoint c p)).1) ((qmaLaneDown C (qmaLanePoint c q)).1) ≤
        (qmaLaneDown C z).1 ∧ (qmaLaneDown C z).1 ≤
        max ((qmaLaneDown C (qmaLanePoint c p)).1) ((qmaLaneDown C (qmaLanePoint c q)).1) at h
      simpa only [qmaBetween,hdownp,hdownq] using h
  · right
    refine ⟨?_,?_⟩
    · have h := congrArg (fun x => x/C) hx
      change (qmaLaneDown C z).1 = (qmaLaneDown C (qmaLanePoint c q)).1 at h
      rw [hdownq] at h
      exact h
    · have h := qmaQuotient_bounds _ _ _ C hy.1 hy.2
      change min ((qmaLaneDown C (qmaLanePoint c p)).2) ((qmaLaneDown C (qmaLanePoint c q)).2) ≤
        (qmaLaneDown C z).2 ∧ (qmaLaneDown C z).2 ≤
        max ((qmaLaneDown C (qmaLanePoint c p)).2) ((qmaLaneDown C (qmaLanePoint c q)).2) at h
      simpa only [qmaBetween,hdownp,hdownq] using h

theorem qmaLaneSupport_disjoint {C : ℕ} (c : Fin C) {p q u v : ℕ × ℕ}
    (h : Disjoint {z | qmaManhattanSupport p q z} {z | qmaManhattanSupport u v z}) :
    Disjoint {z | qmaLaneSupport c p q z} {z | qmaLaneSupport c u v z} := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  exact Set.disjoint_left.mp h (qmaLaneSupport_down c hz) (qmaLaneSupport_down c hz')

theorem qmaLaneSupport_transverse {C : ℕ} {c d : Fin C} (hcd : c ≠ d)
    {p q u v z : ℕ × ℕ} (hc : qmaLaneSupport c p q z) (hd : qmaLaneSupport d u v z) :
    (qmaHorizontalLane c p.2 z ∧ qmaVerticalLane d v.1 z) ∨
      (qmaVerticalLane c q.1 z ∧ qmaHorizontalLane d u.2 z) := by
  rcases hc with ⟨hc,_⟩ | ⟨hc,_⟩ <;> rcases hd with ⟨hd,_⟩ | ⟨hd,_⟩
  · exact (hcd (qmaHorizontalLane_color hc hd)).elim
  · exact Or.inl ⟨hc,hd⟩
  · exact Or.inr ⟨hc,hd⟩
  · exact (hcd (qmaVerticalLane_color hc hd)).elim

theorem qmaLaneSupport_crossing_not_vertex {C : ℕ} {c d : Fin C} (hcd : c ≠ d)
    {p q u v z : ℕ × ℕ} (hc : qmaLaneSupport c p q z) (hd : qmaLaneSupport d u v z)
    (e : Fin C) (w : ℕ × ℕ) : z ≠ qmaLanePoint e w := by
  rcases qmaLaneSupport_transverse hcd hc hd with ⟨hh,hv⟩ | ⟨hv,hh⟩
  · exact qmaLane_crossing_not_vertex hcd hh hv e w
  · exact qmaLane_crossing_not_vertex hcd.symm hh hv e w

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumExchangeLanes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separated lanes for the actual spatial exchange family. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaGridColorEquiv (B : ℕ) : (Fin 3 × Fin 3 × Fin B) ≃ Fin (9*B) :=
  ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv).trans
    (finCongr (by omega))

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

def qmaCrossingMember : Fin 4 → Fin 2 := ![0,0,1,1]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEndpointPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The at-most-three incident edges are assigned distinct, ordered buffered ports. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

structure QMASortedPorts {κ : Type} (C : ℕ) (color : κ → Fin C) where
  slot : Fin 3 → Fin (C+3)
  increasing : StrictMono slot
  assign : κ → Fin 3
  aligned : ∀ e, slot (assign e) = (color e).castAdd 3

def qmaPaddedPortSlot {C : ℕ} (s : Finset (Fin C)) (a : Fin 3) : Fin (C+3) :=
  if h : a.val < s.card then (s.orderEmbOfFin rfl ⟨a.val,h⟩).castAdd 3
  else ⟨C+(a.val-s.card),by have := a.isLt; omega⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedLanes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eightfold lane spacing leaves room for the buffered endpoint arms. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaSpacedLaneColor {C : ℕ} (c : Fin C) : Fin (8*(C+6)) := ⟨8*(c.val+3),by omega⟩

theorem qmaSpacedLaneColor_injective (C : ℕ) : Function.Injective (@qmaSpacedLaneColor C) := by
  intro a b h
  apply Fin.ext
  have hh := congrArg Fin.val h
  dsimp [qmaSpacedLaneColor] at hh
  omega

theorem qmaSpacedEndpoint {C : ℕ} (p : ℕ × ℕ) (c : Fin C) :
    qmaLanePoint (qmaSpacedLaneColor c) p =
      qmaBufferedCellPoint C p (8*(c.val+3),8*(c.val+3)) := by
  apply Prod.ext <;> dsimp [qmaSpacedLaneColor,qmaLanePoint,qmaBufferedCellPoint]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Buffered arms are mutually disjoint away from their common graph vertex. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaBufferedCellPoint_injective (C : ℕ) (p : ℕ × ℕ) :
    Function.Injective (qmaBufferedCellPoint C p) := by
  intro x y h
  apply Prod.ext
  · exact Nat.add_left_cancel (congrArg Prod.fst h)
  · exact Nat.add_left_cancel (congrArg Prod.snd h)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial coefficient and operator bounds for the crossing construction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

def qmaCrossingLeft : Fin 4 → Fin 4 := ![0,0,1,2]
def qmaCrossingRight : Fin 4 → Fin 4 := ![1,3,2,3]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingsGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary spin edges and polynomial full-space error for a parallel crossing-elimination round. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ν : Type*} [Fintype ν]

def qmaCrossingsBaseLeft {n r : ℕ} (left : ν → Fin n) (site : Fin r → Fin 4 → Fin n) :
    ν ⊕ (Fin r × Fin 4) → Fin n := Sum.elim left (fun p => site p.1 (qmaCrossingLeft p.2))
def qmaCrossingsBaseRight {n r : ℕ} (right : ν → Fin n) (site : Fin r → Fin 4 → Fin n) :
    ν ⊕ (Fin r × Fin 4) → Fin n := Sum.elim right (fun p => site p.1 (qmaCrossingRight p.2))

omit [Fintype ν] in
theorem qmaCrossingsBase_distinct {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (site : Fin r → Fin 4 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) :
    ∀ a, qmaCrossingsBaseLeft left site a ≠ qmaCrossingsBaseRight right site a := by
  intro a
  cases a with
  | inl a => exact hneq a
  | inr p =>
    intro h
    have hh := hsite p.1 h
    rcases p with ⟨e,a⟩
    fin_cases a <;> norm_num [qmaCrossingLeft,qmaCrossingRight, Fin.ext_iff] at hh

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial rational programs for the crossing coefficients and penalty. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingCode
open ExactQuantumFactoring.BitStackProgram

abbrev Triple := ℚ × (ℚ × ℚ)

def coefficients (x : Triple) : Fin 10 → ℚ :=
  ![x.1^2,x.1,x.1,2*x.1*x.2.1,2*x.1*x.2.2,
    1/2,-x.2.2,-x.2.1,2*x.2.1*x.2.2,3/2+3*x.2.1^2+3*x.2.2^2+3*x.1^2]

end ContinuumCoulomb.QuantumRoutingCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedPortRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed number of rational mediator layers realizes every bounded spatial
route on its explicit port graph, with full-space energy comparison. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ}

def routeLengthBound (A B : ℕ) : ℕ := 2*(16*(9*B+6)+2)+8*(9*B+9)*(3*A+2)

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathPolynomialBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial coefficient envelopes for the actual selected path
subdivision, uniform in the selected set and its parity choices. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaPathBudget (m L : ℝ) : ℝ :=
  3*m*L+L+3*m*(1+2*L)+4*m*(1+L)^2+1

def qmaPathRadiusBound (m L T : ℝ) : ℝ :=
  L+16*(qmaPathBudget m L)^3*T+4*qmaPathBudget m L+1

def qmaPathCoefficientBound (m L T : ℝ) : ℝ :=
  1+L+(7*m+2)*(qmaPathRadiusBound m L T)^2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingCoefficientBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial coefficient envelopes for the actual rational crossing layer.
The bounds include its scalar counterterms. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaCrossingBudget (m r L : ℝ) : ℝ :=
  3*m*L+L+6*r*(1+2*L)+12*r*(1+2*L)^2+1

def qmaCrossingRadiusBound (m r L T : ℝ) : ℝ :=
  L+16*(qmaCrossingBudget m r L)^3*T+4*qmaCrossingBudget m r L+1

def qmaCrossingCoefficientBound (m r L T : ℝ) : ℝ :=
  1+L+(11*r+2)*(qmaCrossingRadiusBound m r L T)^2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathIteratedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed number of routed subdivisions has an explicit polynomial envelope,
with edge counts tracked separately from coefficient magnitudes. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaPathIteratedBound (m L T : ℝ) : ℕ → ℝ
  | 0 => L
  | k+1 => qmaPathCoefficientBound (3^k*m) (qmaPathIteratedBound m L T k) T

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCoefficientPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal unary programs for the actual routing coefficient envelopes.
Their output lengths give polynomial bounds without choosing giant exponents. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCoefficientPrograms
open ExactQuantumFactoring.BitStackProgram

abbrev Input := ℕ × (ℕ × ℕ)

def pathBudget (m L : ℕ) : ℕ := 3*m*L+L+3*m*(1+2*L)+4*m*(1+L)^2+1
def pathRadius (m L T : ℕ) : ℕ := L+16*(pathBudget m L)^3*T+4*pathBudget m L+1
def pathCoefficient (m L T : ℕ) : ℕ := 1+L+(7*m+2)*(pathRadius m L T)^2

def iterated (m L T : ℕ) : ℕ → ℕ
  | 0 => L
  | k+1 => pathCoefficient (3^k*m) (iterated m L T k) T

@[simp] theorem pathBudget_cast (m L : ℕ) : (pathBudget m L:ℝ) = qmaPathBudget m L := by
  simp [pathBudget,qmaPathBudget]
@[simp] theorem pathRadius_cast (m L T : ℕ) : (pathRadius m L T:ℝ) = qmaPathRadiusBound m L T := by
  simp [pathRadius,qmaPathRadiusBound]
@[simp] theorem pathCoefficient_cast (m L T : ℕ) :
    (pathCoefficient m L T:ℝ) = qmaPathCoefficientBound m L T := by
  simp [pathCoefficient,qmaPathCoefficientBound]
@[simp] theorem iterated_cast (m L T k : ℕ) :
    (iterated m L T k:ℝ) = qmaPathIteratedBound m L T k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iterated,pathCoefficient_cast,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,ih,qmaPathIteratedBound]

def crossingBudget (m r L : ℕ) : ℕ := 3*m*L+L+6*r*(1+2*L)+12*r*(1+2*L)^2+1
def crossingRadius (m r L T : ℕ) : ℕ := L+16*(crossingBudget m r L)^3*T+4*crossingBudget m r L+1
def crossingCoefficient (m r L T : ℕ) : ℕ := 1+L+(11*r+2)*(crossingRadius m r L T)^2

@[simp] theorem crossingBudget_cast (m r L : ℕ) :
    (crossingBudget m r L:ℝ) = qmaCrossingBudget m r L := by simp [crossingBudget,qmaCrossingBudget]
@[simp] theorem crossingRadius_cast (m r L T : ℕ) :
    (crossingRadius m r L T:ℝ) = qmaCrossingRadiusBound m r L T := by simp [crossingRadius,qmaCrossingRadiusBound]
@[simp] theorem crossingCoefficient_cast (m r L T : ℕ) :
    (crossingCoefficient m r L T:ℝ) = qmaCrossingCoefficientBound m r L T := by
  simp [crossingCoefficient,qmaCrossingCoefficientBound]

end ContinuumCoulomb.QuantumCoefficientPrograms

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four distinct ports have the crossing pairing or one of the two corner pairings. -/

namespace ContinuumCoulomb

def qmaPortPairing (f : Fin 4 → Fin 4) : Finset (Sym2 (Fin 4)) :=
  {s(f 0,f 1),s(f 2,f 3)}

def qmaCrossPortPairing : Finset (Sym2 (Fin 4)) := {s(0,2),s(1,3)}

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumInnerPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving crossing terminals one unit into their private patch leaves the
external corridors free and creates space for the two mediator spins. -/

namespace ContinuumCoulomb

def qmaGadgetAncilla (p : ℕ × ℕ) (b : Fin 2) : ℕ × ℕ :=
  ![(32*p.1+14,32*p.2+18),(32*p.1+18,32*p.2+14)] b

theorem qmaGadgetAncilla_cell (p : ℕ × ℕ) (a : Fin 2) :
    ((qmaGadgetAncilla p a).1/32,(qmaGadgetAncilla p a).2/32) = p := by
  apply Prod.ext <;> fin_cases a <;> simp [qmaGadgetAncilla,Nat.add_div]

theorem qmaGadgetAncilla_injective : Function.Injective
    (fun x : (ℕ × ℕ) × Fin 2 => qmaGadgetAncilla x.1 x.2) := by
  rintro ⟨p,a⟩ ⟨q,b⟩ h
  have he := congrArg (fun z : ℕ × ℕ => (z.1/32,z.2/32)) h
  simp only [qmaGadgetAncilla_cell] at he
  subst q
  have hx := congrArg Prod.fst h
  have hab : a = b := by fin_cases a <;> fin_cases b <;> simp [qmaGadgetAncilla] at hx ⊢
  subst b
  rfl

def qmaPortIndex (z : ℕ × ℕ) : Fin 4 :=
  if z.1%32 = 23 then 0 else if z.2%32 = 23 then 1 else if z.1%32 = 9 then 2 else 3

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortCrossingSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select and remove the actual finite crossing cells in a completed rational
port graph. The gadget terminals are existing physical spins. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaPatchDirection : Fin 4 → Fin 4 := ![2,1,0,3]

theorem qmaPatchDirection_injective : Function.Injective qmaPatchDirection := by decide

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRetainedCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every edge internal to a selected crossing is removed from the retained
graph. The assertion concerns the actual completed subdivision graph. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaCrossPair_direction (a b : Fin 4) (h : s(a,b) ∈ qmaCrossPortPairing) :
    ∃ t : Fin 2,
      (a = qmaPatchDirection (if t = 0 then 0 else 1) ∧
       b = qmaPatchDirection (if t = 0 then 2 else 3)) ∨
      (a = qmaPatchDirection (if t = 0 then 2 else 3) ∧
       b = qmaPatchDirection (if t = 0 then 0 else 1)) := by
  have hfinite : ∀ a b : Fin 4, s(a,b) ∈ qmaCrossPortPairing →
      ∃ t : Fin 2,
        (a = qmaPatchDirection (if t = 0 then 0 else 1) ∧
         b = qmaPatchDirection (if t = 0 then 2 else 3)) ∨
        (a = qmaPatchDirection (if t = 0 then 2 else 3) ∧
         b = qmaPatchDirection (if t = 0 then 0 else 1)) := by decide
  exact hfinite a b h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCorridorEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Either half of a corridor determines its unordered physical endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaCorridorHalfMode (b c : Bool) (t : Fin 2) : Bool := if t = 0 then b else c

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTranslatedInternalSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cell-local disjointness extends to the actual translated physical paths. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaInterior_reverse (l : List (ℕ × ℕ)) :
    (((l.reverse).drop 1).dropLast).toFinset = ((l.drop 1).dropLast).toFinset := by
  simp only [List.drop_one,List.tail_reverse,List.dropLast_reverse,List.tail_dropLast,List.toFinset_reverse]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCorridorInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An interior corridor point belongs to the nonterminal part of one of its
two cell-local halves. -/

namespace ContinuumCoulomb

theorem qmaListInterior_ne_head {α : Type*} {l : List α} (hl : l.Nodup)
    {z a : α} (ha : l.head? = some a) (hz : z ∈ (l.drop 1).dropLast) : z ≠ a := by
  obtain ⟨t,rfl⟩ := List.head?_eq_some_iff.mp ha
  have ht : z ∈ t := List.mem_of_mem_dropLast hz
  intro h
  subst z
  exact (List.nodup_cons.mp hl).1 ht

theorem qmaListInterior_ne_last {l : List (ℕ × ℕ)} (hl : l.Nodup)
    {z a : ℕ × ℕ} (ha : l.getLast? = some a) (hz : z ∈ (l.drop 1).dropLast) : z ≠ a := by
  apply qmaListInterior_ne_head (List.nodup_reverse.mpr hl)
  · simpa only [List.head?_reverse] using ha
  · apply List.mem_toFinset.mp
    rw [qmaInterior_reverse]
    exact List.mem_toFinset.mpr hz

theorem qmaList_mem_drop_one {α : Type*} {l : List α} {z a : α}
    (ha : l.head? = some a) (hz : z ∈ l) (hne : z ≠ a) : z ∈ l.drop 1 := by
  obtain ⟨t,rfl⟩ := List.head?_eq_some_iff.mp ha
  rcases List.mem_cons.mp hz with h | h
  · exact (hne h).elim
  · exact h

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRouteLeaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reserve one singlet leaf beside the initial step of every scaled route.
Four incident directions use four different quadrants. -/

namespace ContinuumCoulomb

def qmaLeafCenter (p : ℕ × ℕ) : ℕ × ℕ := (8*p.1+4,8*p.2+4)

def qmaLeafFirst (p : ℕ × ℕ) : Fin 4 → ℕ × ℕ :=
  ![(8*p.1+5,8*p.2+4),(8*p.1+4,8*p.2+5),
    (8*p.1+3,8*p.2+4),(8*p.1+4,8*p.2+3)]

def qmaRouteLeaf (p : ℕ × ℕ) : Fin 4 → ℕ × ℕ :=
  ![(8*p.1+5,8*p.2+5),(8*p.1+3,8*p.2+5),
    (8*p.1+3,8*p.2+3),(8*p.1+5,8*p.2+3)]

theorem qmaRouteLeaf_cell (p : ℕ × ℕ) (a : Fin 4) :
    ((qmaRouteLeaf p a).1/8,(qmaRouteLeaf p a).2/8) = p := by
  apply Prod.ext <;> fin_cases a <;> simp [qmaRouteLeaf,Nat.add_div]

theorem qmaRouteLeaf_not_gridline (p : ℕ × ℕ) (a : Fin 4) :
    (qmaRouteLeaf p a).1%8 ≠ 4 ∧ (qmaRouteLeaf p a).2%8 ≠ 4 := by
  fin_cases a <;> norm_num [qmaRouteLeaf,Nat.add_mod]

theorem qmaRouteLeaf_avoids (p z : ℕ × ℕ) (a : Fin 4)
    (hz : z.1%8 = 4 ∨ z.2%8 = 4) : qmaRouteLeaf p a ≠ z := by
  intro he
  obtain ⟨hx,hy⟩ := qmaRouteLeaf_not_gridline p a
  rw [he] at hx hy
  exact hz.elim hx hy

theorem qmaRouteLeaf_injective : Function.Injective
    (fun x : (ℕ × ℕ) × Fin 4 => qmaRouteLeaf x.1 x.2) := by
  rintro ⟨p,a⟩ ⟨q,b⟩ h
  have hpq : p = q := by
    have he := congrArg (fun z : ℕ × ℕ => (z.1/8,z.2/8)) h
    simpa only [qmaRouteLeaf_cell] using he
  subst q
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  have hab : a = b := by
    fin_cases a <;> fin_cases b <;> simp [qmaRouteLeaf] at hx hy ⊢
  subst b
  rfl

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumScaledDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior points of two scaled unit segments can coincide only when the
underlying grid edge is the same, possibly with reversed orientation. -/

namespace ContinuumCoulomb

def qmaScaledDirectionPoint (p : ℕ × ℕ) (a : Fin 4) (k : ℕ) : ℕ × ℕ :=
  ![(8*p.1+4+k,8*p.2+4),(8*p.1+4,8*p.2+4+k),
    (8*p.1+4-k,8*p.2+4),(8*p.1+4,8*p.2+4-k)] a

theorem qmaScaledDirectionPoint_not_center (p r : ℕ × ℕ)
    (a : Fin 4) {k : ℕ} (hk : 0 < k) (hk8 : k < 8) :
    qmaScaledDirectionPoint p a k ≠ qmaLeafCenter r := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  fin_cases a <;> simp [qmaScaledDirectionPoint,qmaLeafCenter] at h1 h2 <;> omega

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLatticeSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert an actual simple rational grid graph into the field-free source
Hamiltonian, retaining the exact scalar shift in its thresholds. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaGridCoordinate (p : ℕ × ℕ) : ℤ × ℤ := (p.1,p.2)

theorem qmaGridCoordinate_injective : Function.Injective qmaGridCoordinate := by
  intro p q h
  apply Prod.ext
  · exact_mod_cast (show (p.1:ℤ) = q.1 from congrArg Prod.fst h)
  · exact_mod_cast (show (p.2:ℤ) = q.2 from congrArg Prod.snd h)

theorem qmaNatDistance (a b : ℕ) : Int.natAbs ((a:ℤ)-b) = Nat.dist a b := by
  rcases le_total a b with h | h
  · rw [Int.natAbs_natCast_sub_natCast_of_le h,Nat.dist_eq_sub_of_le h]
  · rw [Int.natAbs_natCast_sub_natCast_of_ge h,Nat.dist_eq_sub_of_le_right h]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLatticeCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The specified physical lattice has a polynomial coefficient envelope,
including both crossing offsets and the final merge of parallel edges. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QuantumCoefficientPrograms

def latticeBound (D m r L T : ℕ) : ℕ :=
  let m₁ := 3^D*m
  let L₁ := iterated m L T D
  let m₂ := m₁+9*r
  let L₂ := crossingCoefficient m₁ r ((m₁+1)*L₁) T
  let L₃ := (m₂+1)*L₂
  let L₄ := iterated (3*m₂) (pathCoefficient m₂ L₃ T) T 80
  (3^81*m₂+1)*L₄

end QuantumCoefficientPrograms

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLatticeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal polynomial program computes the final coefficient envelope;
the exponent in the source promise is uniform over all inputs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCoefficientPrograms
open ExactQuantumFactoring.BitStackProgram

abbrev LatticeInput := ℕ × (ℕ × (ℕ × ℕ))

end ContinuumCoulomb.QuantumCoefficientPrograms

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedXZTerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic X/Z term classification from a list of at most two sites.
The order of pair endpoints is the supplied order, with no finite-set choice. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedXZTerm
open scoped Classical

def axis (a : Fin 4) : Fin 2 := if a = 1 then 0 else 1

def field {n : ℕ} (w : Fin n → Fin 4) (i : Fin n) : QMAXZTerm n :=
  if w i = 0 then .scalar else .field i (axis (w i))

def ofSites {n : ℕ} (xs : List (Fin n)) (w : Fin n → Fin 4) : QMAXZTerm n :=
  match xs with
  | [] => .scalar
  | [i] => field w i
  | i :: j :: _ =>
      if h : i = j then field w i
      else if w i = 0 then field w j
      else if w j = 0 then field w i
      else .pair i j h (axis (w i)) (axis (w j))

end ContinuumCoulomb.QuantumOrderedXZTerm

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedRawPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Raw scalar/field/pair instructions read directly from the ordered
site-label list. Only two entries are inspected at the final X/Z stage. -/

namespace ContinuumCoulomb.QuantumOrderedRawPacking

abbrev Letter := ℕ × ℕ
abbrev Input := List Letter × ℚ

def scalar (j : ℚ) : QuantumRawExchange.Raw :=
  ((false,false),((0,0),((false,false),j)))

def field (u : Letter) (j : ℚ) : QuantumRawExchange.Raw :=
  if u.2 = 0 then scalar j else
    ((false,true),((u.1,0),((decide (u.2=1),false),j)))

def pair (u v : Letter) (j : ℚ) : QuantumRawExchange.Raw :=
  ((true,false),((u.1,v.1),((decide (u.2=1),decide (v.2=1)),j)))

def value (x : Input) : QuantumRawExchange.Raw :=
  match x.1 with
  | [] => scalar x.2
  | [u] => field u x.2
  | u :: v :: _ => if u.1=v.1 then field u x.2 else
      if u.2=0 then field v x.2 else
      if v.2=0 then field u x.2 else pair u v x.2

theorem axis_zero (a : Fin 4) :
    decide (QuantumOrderedXZTerm.axis a = 0) = decide (a.val = 1) := by
  fin_cases a <;> rfl

theorem field_pack {n : ℕ} (w : Fin n → Fin 4) (i : Fin n) (j : ℚ) :
    field (i.val,(w i).val) j = QuantumRawExchange.pack (QuantumOrderedXZTerm.field w i) j := by
  by_cases hi : w i = 0
  · simp [field,scalar,QuantumOrderedXZTerm.field,hi,QuantumRawExchange.pack]
  · have hv : (w i).val ≠ 0 := fun h => hi (Fin.ext h)
    simp only [field,hv,ite_false, if_false,QuantumOrderedXZTerm.field,hi,QuantumRawExchange.pack,
      axis_zero]

end ContinuumCoulomb.QuantumOrderedRawPacking

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounding a finite Pauli family controls its actual full-space ground energy. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def qmaPauliFamily (w : κ → ι → Fin 4) (J : κ → ℝ) : Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  ∑ e, (J e:ℂ) • qmaPauliWord (w e)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic balanced support factors.  The actual compiler carries
ordered lists of sites and splits them with take/drop; no chosen finite
subset is needed by either subdivision stage. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSplit
open Matrix
open scoped BigOperators Classical
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def left (xs : List ι) (d : ℕ) : Finset ι := (xs.take d).toFinset
def right (xs : List ι) (d : ℕ) : Finset ι := (xs.drop d).toFinset

def firstWord (xs : List ι) (d : ℕ) (w : ι → Fin 4) : ι → Fin 4 :=
  qmaPauliRestrict (left xs d) w

def secondWord (xs : List ι) (d : ℕ) (w : ι → Fin 4) : ι → Fin 4 :=
  qmaPauliRestrict (right xs d) w

end ContinuumCoulomb.QuantumOrderedSplit

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPolarizedSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal four-word subdivision for even-Y interactions.  The mediator
letter is Y precisely when each input factor has odd Y parity.  All output
coefficients are rational when the input coefficient and scale are rational. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPolarizedSubdivision
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def axis (p : Bool) : Fin 4 := if p then 2 else 1

def word (a b : ι → Fin 4) (e : κ) (m : κ → Bool) :
    Fin 4 → (ι ⊕ κ → Fin 4) :=
  ![fun _ => 0,Sum.elim (fun _ => 0) (qmaSinglePauliWord e 3),
    Sum.elim a (qmaSinglePauliWord e (axis (m e))),
    Sum.elim b (qmaSinglePauliWord e (axis (m e)))]

def weight (R j : ℚ) : Fin 4 → ℚ :=
  ![R^2/2+1+(j/2)^2,-R^2/2,R,-R*j/2]

end ContinuumCoulomb.QuantumPolarizedSubdivision

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit simultaneous subdivision of an ordered rational Pauli
family.  This is the actual four-word Hamiltonian, with a rational scale
and a full-space ground-energy estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSubdivision
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def budget (J : κ → ℚ) : ℚ := 4*(1+∑ e, (1+|J e|)^2)
def scale (J : κ → ℚ) (N : ℕ) : ℚ := 8*(budget J)^4*N

def phase (xs : κ → List ι) (d : ℕ) (w : κ → ι → Fin 4) : κ → Bool :=
  fun e => decide (Odd (qmaPauliYCount (QuantumOrderedSplit.firstWord (xs e) d (w e))))

def outputWord (xs : κ → List ι) (d : ℕ) (w : κ → ι → Fin 4) :
    κ × Fin 4 → (ι ⊕ κ → Fin 4) :=
  fun p => QuantumPolarizedSubdivision.word
    (QuantumOrderedSplit.firstWord (xs p.1) d (w p.1))
    (QuantumOrderedSplit.secondWord (xs p.1) d (w p.1)) p.1 (phase xs d w) p.2

def outputCoefficient (J : κ → ℚ) (N : ℕ) (p : κ × Fin 4) : ℚ :=
  QuantumPolarizedSubdivision.weight (scale J N) (J p.1) p.2

end ContinuumCoulomb.QuantumOrderedSubdivision

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedTriple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A deterministic three-site partition for the third-order gadget.
For three sites the last factor is the first available non-Y letter;
shorter lists give an empty last factor. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedTriple
open scoped Classical
variable {ι : Type}

def partition (xs : List ι) (w : ι → Fin 4) : List ι × List ι :=
  match xs with
  | [a,b,c] => if w a = 2 then
      if w b = 2 then ([a,b],[c]) else ([a,c],[b])
    else ([b,c],[a])
  | _ => (xs,[])

theorem partition_spec (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3) :
    ((partition xs w).1++(partition xs w).2).Perm xs ∧
      (partition xs w).1.length ≤ 2 ∧ (partition xs w).2.length ≤ 1 := by
  cases xs with
  | nil => simp [partition]
  | cons a xs =>
    cases xs with
    | nil => simp [partition]
    | cons b xs =>
      cases xs with
      | nil => simp [partition]
      | cons c xs =>
        cases xs with
        | nil =>
          by_cases ha : w a = 2
          · by_cases hb : w b = 2
            · simp [partition,ha,hb]
            · refine ⟨?_,by simp [partition,ha,hb]⟩
              simpa [partition,ha,hb] using
                (List.Perm.cons a (List.perm_append_comm (l₁ := [c]) (l₂ := [b])))
          · refine ⟨?_,by simp [partition,ha]⟩
            simpa [partition,ha] using (List.perm_append_comm (l₁ := [b,c]) (l₂ := [a]))
        | cons d xs => simp at hlen; omega

theorem partition_nodup (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3)
    (hx : xs.Nodup) : ((partition xs w).1++(partition xs w).2).Nodup :=
  (partition_spec xs w hlen).1.nodup_iff.mpr hx

theorem pair_nodup (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3)
    (hx : xs.Nodup) : (partition xs w).1.Nodup :=
  (partition_nodup xs w hlen hx).of_append_left

end ContinuumCoulomb.QuantumOrderedTriple

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedTripleFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Pauli factors from the ordered three-site partition.  The first
two factors have matching Y parity and the last is real. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedTriple
open scoped Classical
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def first (xs : List ι) (w : ι → Fin 4) : ι → Fin 4 :=
  QuantumOrderedSplit.firstWord (partition xs w).1 1 w

def second (xs : List ι) (w : ι → Fin 4) : ι → Fin 4 :=
  QuantumOrderedSplit.secondWord (partition xs w).1 1 w

def third (xs : List ι) (w : ι → Fin 4) : ι → Fin 4 :=
  qmaPauliRestrict (partition xs w).2.toFinset w

def pairWord (xs : List ι) (w : ι → Fin 4) : ι → Fin 4 :=
  qmaPauliRestrict (partition xs w).1.toFinset w

end ContinuumCoulomb.QuantumOrderedTriple

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPolarizedThird
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Seven literal rational Pauli words for the real-preserving third-order
gadget.  The two possibly imaginary factors use the same mediator phase. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPolarizedThird
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def word (a b c v : ι → Fin 4) (e : κ) (m : κ → Bool) :
    Fin 7 → (ι ⊕ κ → Fin 4) :=
  ![fun _ => 0, Sum.elim (fun _ => 0) (qmaSinglePauliWord e 3),
    Sum.elim v (fun _ => 0), Sum.elim c (fun _ => 0),
    Sum.elim c (qmaSinglePauliWord e 3),
    Sum.elim a (qmaSinglePauliWord e (QuantumPolarizedSubdivision.axis (m e))),
    Sum.elim b (qmaSinglePauliWord e (QuantumPolarizedSubdivision.axis (m e)))]

def weight (R j : ℚ) : Fin 7 → ℚ :=
  ![R^3/2+R*(1+(j/2)^2), -R^3/2, R*j, R^2/2-(1+(j/2)^2),
    -R^2/2, R^2, R^2*j/2]

end ContinuumCoulomb.QuantumPolarizedThird

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedThird
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal simultaneous rational three-to-two-local reduction, with
ordered factors and an ordinary full-Hilbert-space energy estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedThird
open Matrix QuantumOrderedTriple
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def phase (xs : κ → List ι) (w : κ → ι → Fin 4) : κ → Bool :=
  fun e => decide (Odd (qmaPauliYCount (first (xs e) (w e))))

def outputWord (xs : κ → List ι) (w : κ → ι → Fin 4) :
    κ × Fin 7 → (ι ⊕ κ → Fin 4) :=
  fun p => QuantumPolarizedThird.word (first (xs p.1) (w p.1))
    (second (xs p.1) (w p.1)) (third (xs p.1) (w p.1))
    (pairWord (xs p.1) (w p.1)) p.1 (phase xs w) p.2

def outputCoefficient (J : κ → ℚ) (N : ℕ) (p : κ × Fin 7) : ℚ :=
  QuantumPolarizedThird.weight (QuantumOrderedSubdivision.scale J N) (J p.1) p.2

end ContinuumCoulomb.QuantumOrderedThird

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSubdivisionSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal ordered site lists for each of the four subdivision terms.
The two finite subdivision stages reuse these lists, rather than selecting
a new support from an existential locality certificate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSubdivision
open scoped Classical

variable {ι κ : Type}

def appendMediator (xs : List ι) (e : κ) : List (ι ⊕ κ) :=
  xs.map Sum.inl ++ [Sum.inr e]

theorem appendMediator_nodup (xs : List ι) (hx : xs.Nodup) (e : κ) :
    (appendMediator xs e).Nodup := by
  apply (hx.map Sum.inl_injective).append (List.nodup_singleton _)
  intro x hx he
  have hxe : x = Sum.inr e := by simpa using he
  subst x
  simp at hx

theorem appendMediator_length (xs : List ι) (e : κ) :
    (appendMediator xs e).length = xs.length+1 := by
  simp [appendMediator]

def outputSites (xs : κ → List ι) (d : ℕ) (p : κ × Fin 4) : List (ι ⊕ κ) :=
  ![[],[Sum.inr p.1],appendMediator ((xs p.1).take d) p.1,
    appendMediator ((xs p.1).drop d) p.1] p.2

theorem outputSites_nodup (xs : κ → List ι) (d : ℕ)
    (hx : ∀ e, (xs e).Nodup) (p : κ × Fin 4) :
    (outputSites xs d p).Nodup := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · exact List.nodup_nil
  · exact List.nodup_singleton _
  · exact appendMediator_nodup _ ((hx e).sublist (List.take_sublist d _)) e
  · exact appendMediator_nodup _ ((hx e).sublist (List.drop_sublist d _)) e

theorem outputSites_length (xs : κ → List ι) (d : ℕ)
    (hx : ∀ e, (xs e).length ≤ 2*d) (p : κ × Fin 4) :
    (outputSites xs d p).length ≤ d+1 := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · change 0 ≤ d+1
    omega
  · change 1 ≤ d+1
    omega
  · change (appendMediator ((xs e).take d) e).length ≤ d+1
    rw [appendMediator_length,List.length_take]
    omega
  · change (appendMediator ((xs e).drop d) e).length ≤ d+1
    rw [appendMediator_length,List.length_drop]
    have := hx e
    omega

end ContinuumCoulomb.QuantumOrderedSubdivision

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedThirdSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact ordered support lists for the seven emitted third-order terms. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedThird
open QuantumOrderedTriple QuantumOrderedSubdivision
open scoped Classical
variable {ι κ : Type}

def outputSites (xs : κ → List ι) (w : κ → ι → Fin 4) (p : κ × Fin 7) : List (ι ⊕ κ) :=
  let pair := (partition (xs p.1) (w p.1)).1
  let real := (partition (xs p.1) (w p.1)).2
  ![[],[Sum.inr p.1],pair.map Sum.inl,real.map Sum.inl,
    appendMediator real p.1,appendMediator (pair.take 1) p.1,
    appendMediator (pair.drop 1) p.1] p.2

theorem outputSites_nodup (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 3) (hx : ∀ e, (xs e).Nodup) (p : κ × Fin 7) :
    (outputSites xs w p).Nodup := by
  rcases p with ⟨e,k⟩
  have hp := pair_nodup (xs e) (w e) (hlen e) (hx e)
  have hc := (partition_nodup (xs e) (w e) (hlen e) (hx e)).of_append_right
  fin_cases k
  · exact List.nodup_nil
  · exact List.nodup_singleton _
  · exact hp.map Sum.inl_injective
  · exact hc.map Sum.inl_injective
  · exact appendMediator_nodup _ hc e
  · exact appendMediator_nodup _ (hp.sublist (List.take_sublist 1 _)) e
  · exact appendMediator_nodup _ (hp.sublist (List.drop_sublist 1 _)) e

theorem outputSites_length (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 3) (p : κ × Fin 7) :
    (outputSites xs w p).length ≤ 2 := by
  rcases p with ⟨e,k⟩
  have hp := (partition_spec (xs e) (w e) (hlen e)).2.1
  have hc := (partition_spec (xs e) (w e) (hlen e)).2.2
  fin_cases k
  · change 0 ≤ 2
    omega
  · change 1 ≤ 2
    omega
  · change ((partition (xs e) (w e)).1.map Sum.inl).length ≤ 2
    simpa only [List.length_map] using hp
  · change ((partition (xs e) (w e)).2.map Sum.inl).length ≤ 2
    simpa only [List.length_map] using hc.trans (by omega : 1 ≤ 2)
  · change (appendMediator (partition (xs e) (w e)).2 e).length ≤ 2
    rw [appendMediator_length]
    omega
  · change (appendMediator ((partition (xs e) (w e)).1.take 1) e).length ≤ 2
    rw [appendMediator_length,List.length_take]
    omega
  · change (appendMediator ((partition (xs e) (w e)).1.drop 1) e).length ≤ 2
    rw [appendMediator_length,List.length_drop]
    omega

end ContinuumCoulomb.QuantumOrderedThird

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedYYFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal XZ/ZX factors for the only possible real two-site Y term. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedYY
open Matrix
open scoped Classical
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def factor (xs : List ι) (w : ι → Fin 4) : (ι → Fin 4) × (ι → Fin 4) :=
  match xs with
  | [a,b] => if w a = 2 then (qmaTwoPauliWord a b 1 3,qmaTwoPauliWord a b 3 1)
      else (w,fun _ => 0)
  | _ => (w,fun _ => 0)

end ContinuumCoulomb.QuantumOrderedYY

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedYYReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal rational YY-to-XZ subdivision, retaining ordered source sites. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedYY
open Matrix QuantumOrderedSubdivision
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def outputWord (xs : κ → List ι) (w : κ → ι → Fin 4) :
    κ × Fin 4 → (ι ⊕ κ → Fin 4) :=
  fun p => qmaXZSubdivisionWord (factor (xs p.1) (w p.1)).1
    (factor (xs p.1) (w p.1)).2 p.1 p.2

def outputCoefficient (J : κ → ℚ) (N : ℕ) (p : κ × Fin 4) : ℚ :=
  QuantumOrderedSubdivision.outputCoefficient J N p

def outputSites (xs : κ → List ι) (p : κ × Fin 4) : List (ι ⊕ κ) :=
  ![[],[Sum.inr p.1],appendMediator (xs p.1) p.1,appendMediator (xs p.1) p.1] p.2

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem outputSites_nodup (xs : κ → List ι) (hx : ∀ e, (xs e).Nodup)
    (p : κ × Fin 4) : (outputSites xs p).Nodup := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · exact List.nodup_nil
  · exact List.nodup_singleton _
  · exact appendMediator_nodup _ (hx e) e
  · exact appendMediator_nodup _ (hx e) e

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem outputSites_length (xs : κ → List ι) (hlen : ∀ e, (xs e).length ≤ 2)
    (p : κ × Fin 4) : (outputSites xs p).length ≤ 3 := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · change 0 ≤ 3; omega
  · change 1 ≤ 3; omega
  · change (appendMediator (xs e) e).length ≤ 3
    rw [appendMediator_length]
    have := hlen e
    omega
  · change (appendMediator (xs e) e).length ≤ 3
    rw [appendMediator_length]
    have := hlen e
    omega

end ContinuumCoulomb.QuantumOrderedYY

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered sparse site/letter arrays.  Every word carries the already
proved support list; the bounded gadget operations inspect at most six
letters, and retain the original order even for identity letters. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelData
open scoped BigOperators Classical

abbrev Letter := QuantumOrderedRawPacking.Letter

def tag {ι : Type} (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) : List Letter :=
  xs.map (fun i => (index i,(w i).val))

def partition (xs : List Letter) : List Letter × List Letter :=
  match xs with
  | [a,b,c] => if a.2=2 then
      if b.2=2 then ([a,b],[c]) else ([a,c],[b])
    else ([b,c],[a])
  | _ => (xs,[])

def yCount (xs : List Letter) : ℕ := (xs.filter (fun a => a.2=2)).length

def axis (xs : List Letter) : ℕ := if Odd (yCount xs) then 2 else 1

theorem tag_take {ι : Type} (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) (d : ℕ) :
    tag index (xs.take d) w = (tag index xs w).take d := by
  simp only [tag,List.map_take]

theorem tag_drop {ι : Type} (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) (d : ℕ) :
    tag index (xs.drop d) w = (tag index xs w).drop d := by
  simp only [tag,List.map_drop]

theorem partition_tag {ι : Type} (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) :
    partition (tag index xs w) =
      (tag index (QuantumOrderedTriple.partition xs w).1 w,
        tag index (QuantumOrderedTriple.partition xs w).2 w) := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      cases xs with
      | nil => rfl
      | cons c xs =>
        cases xs with
        | cons d xs => rfl
        | nil =>
          have ha : (w a).val=2 ↔ w a=2 := by
            constructor
            · intro h; exact Fin.ext h
            · intro h; exact congrArg Fin.val h
          have hb : (w b).val=2 ↔ w b=2 := by
            constructor
            · intro h; exact Fin.ext h
            · intro h; exact congrArg Fin.val h
          simp only [tag,List.map_cons,List.map_nil,partition,ha,hb,
            QuantumOrderedTriple.partition]
          split_ifs <;> rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem yCount_tag (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4)
    (hx : xs.Nodup) (hw : qmaPauliSupport w ⊆ xs.toFinset) :
    yCount (tag index xs w)=qmaPauliYCount w := by
  have hfilter : (xs.filter (fun i => w i=2)).toFinset =
      Finset.univ.filter (fun i => w i=2) := by
    ext i
    simp only [List.mem_toFinset,List.mem_filter,Finset.mem_filter,
      Finset.mem_univ,true_and,decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨List.mem_toFinset.mp (hw (by simp [qmaPauliSupport,h])),h⟩
  have hcount := List.toFinset_card_of_nodup (hx.filter (fun i => w i=2))
  rw [hfilter] at hcount
  unfold yCount tag
  rw [List.filter_map]
  have hv : (fun i : ι => decide ((w i).val=2)) = (fun i => decide (w i=2)) := by
    funext i
    congr 1
    exact propext ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  simp only [Function.comp_def,hv,List.length_map]
  exact hcount.symm

omit [Fintype ι] in
theorem tag_restrict (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4)
    (ys : List ι) (hys : ∀ i ∈ xs, i ∈ ys) :
    tag index xs (qmaPauliRestrict ys.toFinset w)=tag index xs w := by
  apply List.map_congr_left
  intro i hi
  simp only [qmaPauliRestrict,List.mem_toFinset.mpr (hys i hi),ite_true, if_true]

end ContinuumCoulomb.QuantumOrderedLabelData

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal bounded arrays for polarized subdivision.  The exact array
identity below keeps the supplied site order and the matching mediator. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelData
open scoped Classical

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def subdivision (mediator d : ℕ) (xs : List Letter) : Fin 4 → List Letter :=
  ![[],[(mediator,3)],xs.take d++[(mediator,axis (xs.take d))],
    xs.drop d++[(mediator,axis (xs.take d))]]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem tag_lift (index : ι → ℕ) (slot : κ → ℕ) (xs : List ι)
    (w : ι → Fin 4) (v : κ → Fin 4) :
    tag (Sum.elim index slot) (xs.map Sum.inl) (Sum.elim w v) =tag index xs w := by
  simp only [tag,List.map_map,Function.comp_def,Sum.elim_inl]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] in
theorem tag_appendMediator (index : ι → ℕ) (slot : κ → ℕ) (xs : List ι)
    (w : ι → Fin 4) (e : κ) (a : Fin 4) :
    tag (Sum.elim index slot) (QuantumOrderedSubdivision.appendMediator xs e)
      (Sum.elim w (qmaSinglePauliWord e a)) =tag index xs w++[(slot e,a.val)] := by
  simp only [QuantumOrderedSubdivision.appendMediator,tag,List.map_append,List.map_map,
    Function.comp_def,Sum.elim_inl,List.map_cons,List.map_nil,Sum.elim_inr,
    qmaSinglePauliWord,ite_true, if_true]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem first_tag (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) (d : ℕ) :
    tag index (xs.take d) (QuantumOrderedSplit.firstWord xs d w) =
      (tag index xs w).take d := by
  rw [QuantumOrderedSplit.firstWord,QuantumOrderedSplit.left,
    tag_restrict index (xs.take d) w (xs.take d) (fun _ h => h),tag_take]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem second_tag (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) (d : ℕ) :
    tag index (xs.drop d) (QuantumOrderedSplit.secondWord xs d w) =
      (tag index xs w).drop d := by
  rw [QuantumOrderedSplit.secondWord,QuantumOrderedSplit.right,
    tag_restrict index (xs.drop d) w (xs.drop d) (fun _ h => h),tag_drop]

omit [Fintype κ] [DecidableEq κ] in
theorem first_axis (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4)
    (hx : xs.Nodup) (d : ℕ) :
    axis ((tag index xs w).take d) =
      (QuantumPolarizedSubdivision.axis
        (decide (Odd (qmaPauliYCount (QuantumOrderedSplit.firstWord xs d w))))).val := by
  have hc := yCount_tag index (xs.take d) (QuantumOrderedSplit.firstWord xs d w)
    (hx.sublist (List.take_sublist d xs)) (qmaPauliRestrict_support _ _)
  rw [first_tag] at hc
  simp only [axis,hc,QuantumPolarizedSubdivision.axis,decide_eq_true_eq]
  split_ifs <;> rfl

omit [Fintype κ] in
theorem subdivision_tag (index : ι → ℕ) (slot : κ → ℕ)
    (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hx : ∀ e, (xs e).Nodup) (d : ℕ) (p : κ × Fin 4) :
    tag (Sum.elim index slot) (QuantumOrderedSubdivision.outputSites xs d p)
      (QuantumOrderedSubdivision.outputWord xs d w p) =
      subdivision (slot p.1) d (tag index (xs p.1) (w p.1)) p.2 := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · rfl
  · change tag (Sum.elim index slot) [Sum.inr e]
      (Sum.elim (fun _ : ι => 0) (qmaSinglePauliWord e 3)) = [(slot e,3)]
    simp only [tag,List.map_cons,List.map_nil,Sum.elim_inr,qmaSinglePauliWord,ite_true, if_true]
    rfl
  · change tag (Sum.elim index slot) (QuantumOrderedSubdivision.appendMediator ((xs e).take d) e)
      (Sum.elim (QuantumOrderedSplit.firstWord (xs e) d (w e))
        (qmaSinglePauliWord e (QuantumPolarizedSubdivision.axis
          (QuantumOrderedSubdivision.phase xs d w e)))) =
        (tag index (xs e) (w e)).take d ++
          [(slot e,axis ((tag index (xs e) (w e)).take d))]
    rw [tag_appendMediator,first_tag,first_axis index (xs e) (w e) (hx e)]
    rfl
  · change tag (Sum.elim index slot) (QuantumOrderedSubdivision.appendMediator ((xs e).drop d) e)
      (Sum.elim (QuantumOrderedSplit.secondWord (xs e) d (w e))
        (qmaSinglePauliWord e (QuantumPolarizedSubdivision.axis
          (QuantumOrderedSubdivision.phase xs d w e)))) =
        (tag index (xs e) (w e)).drop d ++
          [(slot e,axis ((tag index (xs e) (w e)).take d))]
    rw [tag_appendMediator,second_tag,first_axis index (xs e) (w e) (hx e)]
    rfl

end ContinuumCoulomb.QuantumOrderedLabelData

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedRawPackingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal polynomial program for the final ordered X/Z classifier.
It reads two site-label pairs and never enumerates a spin basis. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedRawPacking
open ExactQuantumFactoring.BitStackProgram

def entry (k : ℕ) (x : Input) : Letter := (x.1.drop k).headD (0,0)

def lookupValue (x : Input) : QuantumRawExchange.Raw :=
  if x.1.length=0 then scalar x.2 else
  if x.1.length=1 then field (entry 0 x) x.2 else
  if (entry 0 x).1=(entry 1 x).1 then field (entry 0 x) x.2 else
  if (entry 0 x).2=0 then field (entry 1 x) x.2 else
  if (entry 1 x).2=0 then field (entry 0 x) x.2 else
    pair (entry 0 x) (entry 1 x) x.2

theorem lookupValue_eq (x : Input) : lookupValue x = value x := by
  rcases x with ⟨xs,j⟩
  cases xs with
  | nil => rfl
  | cons u xs =>
    cases xs with
    | nil => simp [lookupValue,value,entry]
    | cons v xs => simp [lookupValue,value,entry]

end ContinuumCoulomb.QuantumOrderedRawPacking

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial list programs for the literal support-label operations.
Only constant-length prefixes are split in the early gadget compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelData
open ExactQuantumFactoring.BitStackProgram

def oddLetters (xs : List Letter) : Bool :=
  xs.foldr (fun a b => xor (decide (a.2=2)) b) false

theorem oddLetters_eq (xs : List Letter) :
    oddLetters xs=decide (Odd (yCount xs)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change xor (decide (a.2=2)) (oddLetters xs)=_
    rw [ih]
    by_cases ha : a.2=2
    · have hc : yCount (a::xs)=yCount xs+1 := by simp [yCount,ha]
      simp only [hc,Nat.odd_add_one,ha,decide_true,Bool.true_xor,decide_not]
    · have hc : yCount (a::xs)=yCount xs := by simp [yCount,ha]
      rw [hc]
      simp [ha]

theorem fold_oddLetters (xs : List Letter) (b : Bool) :
    xs.foldl (fun b a => xor (decide (a.2=2)) b) b=xor (oddLetters xs) b := by
  induction xs generalizing b with
  | nil => simp [oddLetters]
  | cons a xs ih =>
    rw [List.foldl_cons,ih]
    change xor (oddLetters xs) (xor (decide (a.2=2)) b)=
      xor (xor (decide (a.2=2)) (oddLetters xs)) b
    cases b <;> cases ha : decide (a.2=2) <;> cases hx : oddLetters xs <;> rfl

abbrev BlockInput := ℕ × List Letter

end ContinuumCoulomb.QuantumOrderedLabelData

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelThird
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered support-label arrays for the seven third-order terms.  The
same literal three-entry partition selects the real factor and the two
matching-parity factors. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelData
open scoped Classical

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def thirdBlock (mediator : ℕ) (xs : List Letter) : Fin 7 → List Letter :=
  let p := partition xs
  ![[],[(mediator,3)],p.1,p.2,p.2++[(mediator,3)],
    p.1.take 1++[(mediator,axis (p.1.take 1))],
    p.1.drop 1++[(mediator,axis (p.1.take 1))]]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem pair_tag (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) :
    tag index (QuantumOrderedTriple.partition xs w).1
      (QuantumOrderedTriple.pairWord xs w)=(partition (tag index xs w)).1 := by
  rw [QuantumOrderedTriple.pairWord,tag_restrict index _ w _ (fun _ h => h)]
  exact (congrArg Prod.fst (partition_tag index xs w)).symm

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem real_tag (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) :
    tag index (QuantumOrderedTriple.partition xs w).2
      (QuantumOrderedTriple.third xs w)=(partition (tag index xs w)).2 := by
  rw [QuantumOrderedTriple.third,tag_restrict index _ w _ (fun _ h => h)]
  exact (congrArg Prod.snd (partition_tag index xs w)).symm

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem third_first_tag (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) :
    tag index ((QuantumOrderedTriple.partition xs w).1.take 1)
      (QuantumOrderedTriple.first xs w)=(partition (tag index xs w)).1.take 1 := by
  rw [QuantumOrderedTriple.first,first_tag]
  exact congrArg (List.take 1) (congrArg Prod.fst (partition_tag index xs w)).symm

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem third_second_tag (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) :
    tag index ((QuantumOrderedTriple.partition xs w).1.drop 1)
      (QuantumOrderedTriple.second xs w)=(partition (tag index xs w)).1.drop 1 := by
  rw [QuantumOrderedTriple.second,second_tag]
  exact congrArg (List.drop 1) (congrArg Prod.fst (partition_tag index xs w)).symm

omit [Fintype κ] [DecidableEq κ] in
theorem third_axis (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4)
    (hlen : xs.length ≤ 3) (hx : xs.Nodup) :
    axis ((partition (tag index xs w)).1.take 1) =
      (QuantumPolarizedSubdivision.axis
        (decide (Odd (qmaPauliYCount (QuantumOrderedTriple.first xs w))))).val := by
  have hp := (congrArg Prod.fst (partition_tag index xs w)).symm
  rw [← hp]
  exact first_axis index _ w (QuantumOrderedTriple.pair_nodup xs w hlen hx) 1

omit [Fintype κ] in
theorem thirdBlock_tag (index : ι → ℕ) (slot : κ → ℕ)
    (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 3) (hx : ∀ e, (xs e).Nodup) (p : κ × Fin 7) :
    tag (Sum.elim index slot) (QuantumOrderedThird.outputSites xs w p)
      (QuantumOrderedThird.outputWord xs w p) =
      thirdBlock (slot p.1) (tag index (xs p.1) (w p.1)) p.2 := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · rfl
  · change tag (Sum.elim index slot) [Sum.inr e]
      (Sum.elim (fun _ : ι => 0) (qmaSinglePauliWord e 3)) = [(slot e,3)]
    simp only [tag,List.map_cons,List.map_nil,Sum.elim_inr,qmaSinglePauliWord,ite_true, if_true]
    rfl
  · change tag (Sum.elim index slot) ((QuantumOrderedTriple.partition (xs e) (w e)).1.map Sum.inl)
      (Sum.elim (QuantumOrderedTriple.pairWord (xs e) (w e)) (fun _ => 0)) = _
    rw [tag_lift,pair_tag]
    rfl
  · change tag (Sum.elim index slot) ((QuantumOrderedTriple.partition (xs e) (w e)).2.map Sum.inl)
      (Sum.elim (QuantumOrderedTriple.third (xs e) (w e)) (fun _ => 0)) = _
    rw [tag_lift,real_tag]
    rfl
  · change tag (Sum.elim index slot)
      (QuantumOrderedSubdivision.appendMediator (QuantumOrderedTriple.partition (xs e) (w e)).2 e)
      (Sum.elim (QuantumOrderedTriple.third (xs e) (w e)) (qmaSinglePauliWord e 3)) = _
    rw [tag_appendMediator,real_tag]
    rfl
  · change tag (Sum.elim index slot)
      (QuantumOrderedSubdivision.appendMediator ((QuantumOrderedTriple.partition (xs e) (w e)).1.take 1) e)
      (Sum.elim (QuantumOrderedTriple.first (xs e) (w e))
        (qmaSinglePauliWord e (QuantumPolarizedSubdivision.axis
          (QuantumOrderedThird.phase xs w e)))) = _
    rw [tag_appendMediator,third_first_tag]
    change _ = (partition (tag index (xs e) (w e))).1.take 1 ++
      [(slot e,axis ((partition (tag index (xs e) (w e))).1.take 1))]
    rw [third_axis index (xs e) (w e) (hlen e) (hx e)]
    rfl
  · change tag (Sum.elim index slot)
      (QuantumOrderedSubdivision.appendMediator ((QuantumOrderedTriple.partition (xs e) (w e)).1.drop 1) e)
      (Sum.elim (QuantumOrderedTriple.second (xs e) (w e))
        (qmaSinglePauliWord e (QuantumPolarizedSubdivision.axis
          (QuantumOrderedThird.phase xs w e)))) = _
    rw [tag_appendMediator,third_second_tag]
    change _ = (partition (tag index (xs e) (w e))).1.drop 1 ++
      [(slot e,axis ((partition (tag index (xs e) (w e))).1.take 1))]
    rw [third_axis index (xs e) (w e) (hlen e) (hx e)]
    rfl

end ContinuumCoulomb.QuantumOrderedLabelData

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedPrivate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal private-pair subdivision of an ordered X/Z family.  The
source site's list order determines both factors and every output site. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedPrivate
open Matrix QuantumOrderedSubdivision
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def outputWord (xs : κ → List ι) (w : κ → ι → Fin 4) :
    κ × Fin 4 → (ι ⊕ κ → Fin 4) :=
  fun p => qmaXZSubdivisionWord
    (QuantumOrderedSplit.firstWord (xs p.1) 1 (w p.1))
    (QuantumOrderedSplit.secondWord (xs p.1) 1 (w p.1)) p.1 p.2

def outputSites (xs : κ → List ι) : κ × Fin 4 → List (ι ⊕ κ) :=
  QuantumOrderedSubdivision.outputSites xs 1

def outputCoefficient (J : κ → ℚ) (N : ℕ) (p : κ × Fin 4) : ℚ :=
  QuantumOrderedSubdivision.outputCoefficient J N p

end ContinuumCoulomb.QuantumOrderedPrivate

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelYY
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact sparse letters for YY removal and the final private-pair split.
Zero-labelled entries are retained so support-list order stays literal. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelData
open scoped Classical

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def zeros (xs : List Letter) : List Letter := xs.map (fun p => (p.1,0))

def yyFactors (xs : List Letter) : List Letter × List Letter :=
  match xs with
  | [a,b] => if a.2=2 then
      ([(a.1,1),(b.1,3)],[(a.1,3),(b.1,1)]) else (xs,zeros xs)
  | _ => (xs,zeros xs)

def yyBlock (mediator : ℕ) (xs : List Letter) : Fin 4 → List Letter :=
  ![[],[(mediator,3)],(yyFactors xs).1++[(mediator,1)],
    (yyFactors xs).2++[(mediator,1)]]

def privateBlock (mediator : ℕ) (xs : List Letter) : Fin 4 → List Letter :=
  ![[],[(mediator,3)],xs.take 1++[(mediator,1)],xs.drop 1++[(mediator,1)]]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem tag_zeros (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) :
    tag index xs (fun _ => 0)=zeros (tag index xs w) := by
  simp only [tag,zeros,List.map_map,Function.comp_def,Fin.val_zero]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem yyFactors_tag (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4)
    (hx : xs.Nodup) :
    (tag index xs (QuantumOrderedYY.factor xs w).1,
      tag index xs (QuantumOrderedYY.factor xs w).2)=yyFactors (tag index xs w) := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil =>
      change (tag index [a] w,tag index [a] (fun _ => 0)) =
        (tag index [a] w,zeros (tag index [a] w))
      exact congrArg (fun z => (tag index [a] w,z)) (tag_zeros index [a] w)
    | cons b xs =>
      cases xs with
      | cons c xs =>
        change (tag index (a::b::c::xs) w,tag index (a::b::c::xs) (fun _ => 0)) =
          (tag index (a::b::c::xs) w,zeros (tag index (a::b::c::xs) w))
        exact congrArg (fun z => (tag index (a::b::c::xs) w,z))
          (tag_zeros index (a::b::c::xs) w)
      | nil =>
        have hab : a ≠ b := by simpa using hx
        have ha : (w a).val=2 ↔ w a=2 :=
          ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
        by_cases h : w a=2
        · simp [QuantumOrderedYY.factor,yyFactors,tag,h,qmaTwoPauliWord,Ne.symm hab]
        · simp only [QuantumOrderedYY.factor,h,ite_false, if_false,tag,List.map_cons,List.map_nil,
            yyFactors,ha]
          exact Prod.ext rfl (tag_zeros index [a,b] w)

omit [Fintype ι] [Fintype κ] in
theorem yyBlock_tag (index : ι → ℕ) (slot : κ → ℕ)
    (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hx : ∀ e, (xs e).Nodup) (p : κ × Fin 4) :
    tag (Sum.elim index slot) (QuantumOrderedYY.outputSites xs p)
      (QuantumOrderedYY.outputWord xs w p) =
      yyBlock (slot p.1) (tag index (xs p.1) (w p.1)) p.2 := by
  rcases p with ⟨e,k⟩
  have hleft := congrArg Prod.fst (yyFactors_tag index (xs e) (w e) (hx e))
  have hright := congrArg Prod.snd (yyFactors_tag index (xs e) (w e) (hx e))
  dsimp only [Prod.fst,Prod.snd] at hleft hright
  fin_cases k
  · rfl
  · change tag (Sum.elim index slot) [Sum.inr e]
      (Sum.elim (fun _ : ι => 0) (qmaSinglePauliWord e 3)) = [(slot e,3)]
    simp only [tag,List.map_cons,List.map_nil,Sum.elim_inr,qmaSinglePauliWord,ite_true, if_true]
    rfl
  · change tag (Sum.elim index slot) (QuantumOrderedSubdivision.appendMediator (xs e) e)
      (Sum.elim (QuantumOrderedYY.factor (xs e) (w e)).1 (qmaSinglePauliWord e 1)) = _
    rw [tag_appendMediator,hleft]
    rfl
  · change tag (Sum.elim index slot) (QuantumOrderedSubdivision.appendMediator (xs e) e)
      (Sum.elim (QuantumOrderedYY.factor (xs e) (w e)).2 (qmaSinglePauliWord e 1)) = _
    rw [tag_appendMediator,hright]
    rfl

omit [Fintype ι] [Fintype κ] in
theorem privateBlock_tag (index : ι → ℕ) (slot : κ → ℕ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (p : κ × Fin 4) :
    tag (Sum.elim index slot) (QuantumOrderedPrivate.outputSites xs p)
      (QuantumOrderedPrivate.outputWord xs w p) =
      privateBlock (slot p.1) (tag index (xs p.1) (w p.1)) p.2 := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · rfl
  · change tag (Sum.elim index slot) [Sum.inr e]
      (Sum.elim (fun _ : ι => 0) (qmaSinglePauliWord e 3)) = [(slot e,3)]
    simp only [tag,List.map_cons,List.map_nil,Sum.elim_inr,qmaSinglePauliWord,ite_true, if_true]
    rfl
  · change tag (Sum.elim index slot) (QuantumOrderedSubdivision.appendMediator ((xs e).take 1) e)
      (Sum.elim (QuantumOrderedSplit.firstWord (xs e) 1 (w e)) (qmaSinglePauliWord e 1)) = _
    rw [tag_appendMediator,first_tag]
    rfl
  · change tag (Sum.elim index slot) (QuantumOrderedSubdivision.appendMediator ((xs e).drop 1) e)
      (Sum.elim (QuantumOrderedSplit.secondWord (xs e) 1 (w e)) (qmaSinglePauliWord e 1)) = _
    rw [tag_appendMediator,second_tag]
    rfl

end ContinuumCoulomb.QuantumOrderedLabelData

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal fixed-size programs for the triple partition and YY/private
blocks. The branch tests inspect only the stored support labels. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelData
open ExactQuantumFactoring.BitStackProgram

def selected (a b : ℕ) (xs : List Letter) : List Letter :=
  [(xs.drop a).headD (0,0),(xs.drop b).headD (0,0)]

def partitionLookup (xs : List Letter) : List Letter × List Letter :=
  if xs.length=3 then
    if ((xs.drop 0).headD (0,0)).2=2 then
      if ((xs.drop 1).headD (0,0)).2=2 then
        (selected 0 1 xs,[(xs.drop 2).headD (0,0)])
      else (selected 0 2 xs,[(xs.drop 1).headD (0,0)])
    else (selected 1 2 xs,[(xs.drop 0).headD (0,0)])
  else (xs,[])

theorem partitionLookup_eq (xs : List Letter) : partitionLookup xs=partition xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      cases xs with
      | nil => rfl
      | cons c xs =>
        cases xs with
        | nil => simp [partitionLookup,partition,selected]
        | cons d xs => simp [partitionLookup,partition,List.length_cons]

def yyLookup (xs : List Letter) : List Letter × List Letter :=
  if xs.length=2 ∧ ((xs.drop 0).headD (0,0)).2=2 then
    ([(((xs.drop 0).headD (0,0)).1,1),(((xs.drop 1).headD (0,0)).1,3)],
     [(((xs.drop 0).headD (0,0)).1,3),(((xs.drop 1).headD (0,0)).1,1)])
  else (xs,zeros xs)
theorem yyLookup_eq (xs : List Letter) : yyLookup xs=yyFactors xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => simp [yyLookup,yyFactors]
    | cons b xs =>
      cases xs with
      | nil => simp [yyLookup,yyFactors]
      | cons c xs => simp [yyLookup,yyFactors,List.length_cons]

end ContinuumCoulomb.QuantumOrderedLabelData

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedTwoStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal rational six-to-four-to-three-local compiler.  Every
intermediate word retains its ordered site list, and the estimate compares
the ordinary full Hilbert-space ground energies. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedTwoStage
open QuantumOrderedSubdivision
open scoped Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def firstWord (xs : κ → List ι) (w : κ → ι → Fin 4) := outputWord xs 3 w
def firstSites (xs : κ → List ι) := outputSites xs 3
def firstCoefficient (J : κ → ℚ) (N : ℕ) := outputCoefficient J N

def word (xs : κ → List ι) (w : κ → ι → Fin 4) :=
  outputWord (firstSites xs) 2 (firstWord xs w)

def sites (xs : κ → List ι) := outputSites (firstSites xs) 2

def coefficient (J : κ → ℚ) (N : ℕ) :=
  outputCoefficient (firstCoefficient J N) N

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem sites_nodup (xs : κ → List ι) (hx : ∀ e, (xs e).Nodup)
    (p : (κ × Fin 4) × Fin 4) : (sites xs p).Nodup :=
  outputSites_nodup _ _ (outputSites_nodup xs 3 hx) p

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem sites_length (xs : κ → List ι) (hx : ∀ e, (xs e).length ≤ 6)
    (p : (κ × Fin 4) × Fin 4) : (sites xs p).length ≤ 3 := by
  apply outputSites_length _ 2
  intro e
  exact outputSites_length xs 3 hx e

end ContinuumCoulomb.QuantumOrderedTwoStage

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedXZPipeline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One literal rational six-local to two-local X/Z family.  The intermediate
types retain the original term index and the bounded gadget-word index. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedXZ
open scoped Classical

abbrev ThreeTerm (κ : Type) := (κ × Fin 4) × Fin 4
abbrev ThreeQubit (ι κ : Type) := (ι ⊕ κ) ⊕ (κ × Fin 4)
abbrev TwoTerm (κ : Type) := ThreeTerm κ × Fin 7
abbrev TwoQubit (ι κ : Type) := ThreeQubit ι κ ⊕ ThreeTerm κ
abbrev XZThreeTerm (κ : Type) := TwoTerm κ × Fin 4
abbrev XZThreeQubit (ι κ : Type) := TwoQubit ι κ ⊕ TwoTerm κ
abbrev OutputTerm (κ : Type) := XZThreeTerm κ × Fin 7
abbrev OutputQubit (ι κ : Type) := XZThreeQubit ι κ ⊕ XZThreeTerm κ

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def threeWord (xs : κ → List ι) (w : κ → ι → Fin 4) :
    ThreeTerm κ → ThreeQubit ι κ → Fin 4 := QuantumOrderedTwoStage.word xs w

def threeSites (xs : κ → List ι) : ThreeTerm κ → List (ThreeQubit ι κ) :=
  QuantumOrderedTwoStage.sites xs

def threeCoefficient (J : κ → ℚ) (N : ℕ) : ThreeTerm κ → ℚ :=
  QuantumOrderedTwoStage.coefficient J N

def twoWord (xs : κ → List ι) (w : κ → ι → Fin 4) :
    TwoTerm κ → TwoQubit ι κ → Fin 4 :=
  QuantumOrderedThird.outputWord (threeSites xs) (threeWord xs w)

def twoSites (xs : κ → List ι) (w : κ → ι → Fin 4) :
    TwoTerm κ → List (TwoQubit ι κ) :=
  QuantumOrderedThird.outputSites (threeSites xs) (threeWord xs w)

def twoCoefficient (J : κ → ℚ) (N : ℕ) : TwoTerm κ → ℚ :=
  QuantumOrderedThird.outputCoefficient (threeCoefficient J N) N

def xzThreeWord (xs : κ → List ι) (w : κ → ι → Fin 4) :
    XZThreeTerm κ → XZThreeQubit ι κ → Fin 4 :=
  QuantumOrderedYY.outputWord (twoSites xs w) (twoWord xs w)

def xzThreeSites (xs : κ → List ι) (w : κ → ι → Fin 4) :
    XZThreeTerm κ → List (XZThreeQubit ι κ) :=
  QuantumOrderedYY.outputSites (twoSites xs w)

def xzThreeCoefficient (J : κ → ℚ) (N : ℕ) : XZThreeTerm κ → ℚ :=
  QuantumOrderedYY.outputCoefficient (twoCoefficient J N) N

def word (xs : κ → List ι) (w : κ → ι → Fin 4) :
    OutputTerm κ → OutputQubit ι κ → Fin 4 :=
  QuantumOrderedThird.outputWord (xzThreeSites xs w) (xzThreeWord xs w)

def sites (xs : κ → List ι) (w : κ → ι → Fin 4) :
    OutputTerm κ → List (OutputQubit ι κ) :=
  QuantumOrderedThird.outputSites (xzThreeSites xs w) (xzThreeWord xs w)

def coefficient (J : κ → ℚ) (N : ℕ) : OutputTerm κ → ℚ :=
  QuantumOrderedThird.outputCoefficient (xzThreeCoefficient J N) N

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem threeSites_nodup (xs : κ → List ι) (hx : ∀ e, (xs e).Nodup) :
    ∀ p, (threeSites xs p).Nodup := QuantumOrderedTwoStage.sites_nodup xs hx

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem threeSites_length (xs : κ → List ι) (hlen : ∀ e, (xs e).length ≤ 6) :
    ∀ p, (threeSites xs p).length ≤ 3 := QuantumOrderedTwoStage.sites_length xs hlen

theorem twoSites_nodup (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup) :
    ∀ p, (twoSites xs w p).Nodup :=
  QuantumOrderedThird.outputSites_nodup _ _
    (threeSites_length xs hlen) (threeSites_nodup xs hx)

theorem twoSites_length (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) : ∀ p, (twoSites xs w p).length ≤ 2 :=
  QuantumOrderedThird.outputSites_length _ _ (threeSites_length xs hlen)

theorem xzThreeSites_nodup (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup) :
    ∀ p, (xzThreeSites xs w p).Nodup :=
  QuantumOrderedYY.outputSites_nodup _ (twoSites_nodup xs w hlen hx)

theorem xzThreeSites_length (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) : ∀ p, (xzThreeSites xs w p).length ≤ 3 :=
  QuantumOrderedYY.outputSites_length _ (twoSites_length xs w hlen)

end ContinuumCoulomb.QuantumOrderedXZ

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

abbrev Input := (ℚ × ℚ) × (List ℚ × List ℚ)

def linearCost (w : ℚ) : ℚ := 1+2*|w|
def squareCost (w : ℚ) : ℚ := (1+|w|)^2
def base (x : Input) : ℚ := 3*(x.2.1.map abs).sum+|x.1.2|
def active (x : Input) : ℚ := 3*(x.2.2.map linearCost).sum
def correction (x : Input) : ℚ := base x+4*(x.2.2.map squareCost).sum
def value (x : Input) : ℚ :=
  16*(active x+correction x+1)^3*x.1.1+4*(active x+correction x+1)+1

end ContinuumCoulomb.QuantumPathScaleProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedWeightProgram
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

abbrev Pair := ℚ × ℚ

abbrev Input := ℕ × List ℚ
def scale (x : Input) : ℚ := 8*(4*(1+(x.2.map (fun j => (1+|j|)^2)).sum))^4*x.1

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

abbrev Entry := List Letter × ℚ
abbrev State := ℕ × List Entry
abbrev Input := ℕ × State
abbrev BlockInput := (ℕ × ℚ) × Entry

def weights (x : Input) : QuantumOrderedWeightProgram.Input := (x.1,x.2.2.map Prod.snd)
def radius (x : Input) : ℚ := QuantumOrderedWeightProgram.scale (weights x)
def indexed (x : ℕ × Input) : BlockInput :=
  ((x.2.2.1+x.1,radius x.2),(x.2.2.2.drop x.1).headD ([],0))

def block (d : ℕ) (f : ℕ → List Letter → Fin d → List Letter)
    (g : ℚ → ℚ → Fin d → ℚ) (x : BlockInput) : List Entry :=
  List.ofFn (fun k => (f x.1.1 x.2.1 k,g x.1.2 x.2.2 k))

def family (d : ℕ) (f : ℕ → List Letter → Fin d → List Letter)
    (g : ℚ → ℚ → Fin d → ℚ) (x : Input) : List Entry :=
  ((List.range x.2.2.length).map (fun i => block d f g (indexed (i,x)))).flatten

def value (d : ℕ) (f : ℕ → List Letter → Fin d → List Letter)
    (g : ℚ → ℚ → Fin d → ℚ) (x : Input) : State :=
  (x.2.1+x.2.2.length,family d f g x)

theorem family_length (d : ℕ)
    (f : ℕ → List Letter → Fin d → List Letter) (g : ℚ → ℚ → Fin d → ℚ)
    (x : Input) : (family d f g x).length=x.2.2.length*d := by
  unfold family
  rw [List.length_flatten,List.map_map]
  simp only [Function.comp_def,block,List.length_ofFn]
  simp

end ContinuumCoulomb.QuantumOrderedLabelFamily

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

abbrev Input := QuantumOrderedLabelFamily.Input
abbrev State := QuantumOrderedLabelFamily.State

def fourWeight (r j : ℚ) := QuantumPolarizedSubdivision.weight r j
def sevenWeight (r j : ℚ) := QuantumPolarizedThird.weight r j

def subdivisionStep (d : ℕ) (x : Input) : Input :=
  (x.1,value 4 (fun n xs => subdivision n d xs) fourWeight x)
def thirdStep (x : Input) : Input := (x.1,value 7 thirdBlock sevenWeight x)
def yyStep (x : Input) : Input := (x.1,value 4 yyBlock fourWeight x)
def privateStep (x : Input) : Input := (x.1,value 4 privateBlock fourWeight x)
def output (x : Input) : State :=
  (privateStep (thirdStep (yyStep (thirdStep (subdivisionStep 2 (subdivisionStep 3 x)))))).2

theorem output_qubits (x : Input) : (output x).1=x.2.1+3717*x.2.2.length := by
  simp only [output,privateStep,thirdStep,yyStep,subdivisionStep,value,family_length]
  omega

end ContinuumCoulomb.QuantumOrderedLabelPipeline

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered finite tables and their literal product enumeration. These
identities compare the computed lists with the actual finite Pauli family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelTable
open QuantumOrderedLabelData QuantumOrderedLabelFamily
open scoped BigOperators Classical

variable {ι κ : Type} {m n d : ℕ}

def table (e : Fin m ≃ κ) (index : ι → ℕ) (xs : κ → List ι)
    (w : κ → ι → Fin 4) (J : κ → ℚ) : List Entry :=
  List.ofFn (fun i => (tag index (xs (e i)) (w (e i)),J (e i)))

def nextTerm (e : Fin m ≃ κ) (d : ℕ) : Fin (m*d) ≃ κ × Fin d :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr e (Equiv.refl _))

def index (q : Fin n ≃ ι) (i : ι) : ℕ := (q.symm i).val

def nextQubit (q : Fin n ≃ ι) (e : Fin m ≃ κ) : Fin (n+m) ≃ ι ⊕ κ :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr q e)

theorem nextQubit_index (q : Fin n ≃ ι) (e : Fin m ≃ κ) :
    index (nextQubit q e) = Sum.elim (index q) (fun a => n+(e.symm a).val) := by
  funext a
  cases a <;> simp [index,nextQubit]

theorem lookup_ofFn {α : Type} (v : Fin m → α) (fallback : α) (i : Fin m) :
    ((List.ofFn v).drop i.val).headD fallback=v i := by
  rw [List.drop_eq_getElem_cons (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.headD_cons,List.getElem_ofFn]

theorem product_table {α : Type} (v : Fin m × Fin d → α) :
    List.ofFn (fun i => v (finProdFinEquiv.symm i)) =
      (List.ofFn (fun a => List.ofFn (fun b => v (a,b)))).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext a
  apply congrArg List.ofFn
  funext b
  have h : finProdFinEquiv (a,b) =
      (⟨a.val*d+b.val,by nlinarith [a.isLt,b.isLt]⟩ : Fin (m*d)) := by
    apply Fin.ext
    change b.val+d*a.val=a.val*d+b.val
    ac_rfl
  rw [← h,Equiv.symm_apply_apply]

variable [Fintype κ]

theorem radius_table (e : Fin m ≃ κ) (ix : ι → ℕ) (xs : κ → List ι)
    (w : κ → ι → Fin 4) (J : κ → ℚ) (N n : ℕ) :
    radius (N,n,table e ix xs w J)=QuantumOrderedSubdivision.scale J N := by
  simp only [radius,weights,table,List.map_ofFn,Function.comp_def,List.sum_ofFn,
    QuantumOrderedWeightProgram.scale,QuantumOrderedSubdivision.scale,
    QuantumOrderedSubdivision.budget]
  rw [e.sum_comp (fun a => (1+|J a|)^2)]

/-- A literal stage is the same product-ordered finite table as its supplied
word and coefficient formulas. The hypotheses are pointwise identities. -/
theorem family_table (e : Fin m ≃ κ) (ix : ι → ℕ) (xs : κ → List ι)
    (w : κ → ι → Fin 4) (J : κ → ℚ) (N n : ℕ)
    (f : ℕ → List Letter → Fin d → List Letter)
    (g : ℚ → ℚ → Fin d → ℚ) :
    family d f g (N,n,table e ix xs w J) =
      List.ofFn (fun i : Fin (m*d) =>
        let p := nextTerm e d i
        (f (n+(e.symm p.1).val) (tag ix (xs p.1) (w p.1)) p.2,
          g (QuantumOrderedSubdivision.scale J N) (J p.1) p.2)) := by
  let v : Fin m → Entry := fun i => (tag ix (xs (e i)) (w (e i)),J (e i))
  have hr := radius_table e ix xs w J N n
  have hrows : (List.range m).map (fun i =>
      block d f g ((n+i,radius (N,n,table e ix xs w J)),((List.ofFn v).drop i).headD ([],0))) =
      List.ofFn (fun a : Fin m => block d f g
        ((n+a.val,QuantumOrderedSubdivision.scale J N),v a)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hi' : i < m := by simpa using hi
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
      rw [hr,lookup_ofFn v ([],0) ⟨i,hi'⟩]
  change ((List.range (List.ofFn v).length).map (fun i =>
    block d f g ((n+i,radius (N,n,table e ix xs w J)),((List.ofFn v).drop i).headD ([],0)))).flatten = _
  rw [List.length_ofFn,hrows]
  symm
  convert product_table (fun p : Fin m × Fin d =>
      (f (n+p.1.val) (v p.1).1 p.2,
        g (QuantumOrderedSubdivision.scale J N) (v p.1).2 p.2)) using 1
  · congr 1
    funext i
    simp only [nextTerm,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_fst,Prod.map_snd,
      Equiv.refl_apply,Equiv.symm_apply_apply,v]
  · rfl

end ContinuumCoulomb.QuantumOrderedLabelTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each literal list stage is exactly the corresponding ordered Pauli
construction, with explicit finite product and sum enumerations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelTable
open QuantumOrderedLabelData QuantumOrderedLabelFamily
open scoped Classical

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {m n d : ℕ}

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem value_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) (N : ℕ)
    (f : ℕ → List Letter → Fin d → List Letter)
    (g : ℚ → ℚ → Fin d → ℚ)
    (ys : κ × Fin d → List (ι ⊕ κ)) (v : κ × Fin d → ι ⊕ κ → Fin 4)
    (h : ∀ p, tag (Sum.elim (index q) (fun a => n+(e.symm a).val)) (ys p) (v p) =
      f (n+(e.symm p.1).val) (tag (index q) (xs p.1) (w p.1)) p.2) :
    value d f g (N,n,table e (index q) xs w J) =
      (n+m,table (nextTerm e d) (index (nextQubit q e)) ys v
        (fun p => g (QuantumOrderedSubdivision.scale J N) (J p.1) p.2)) := by
  apply Prod.ext
  · simp only [value,table,List.length_ofFn]
  · rw [show (value d f g (N,n,table e (index q) xs w J)).2 =
        family d f g (N,n,table e (index q) xs w J) from rfl,
      family_table]
    unfold table
    apply congrArg List.ofFn
    funext i
    dsimp only
    rw [nextQubit_index,h]

theorem subdivision_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hx : ∀ a, (xs a).Nodup) (N cut : ℕ) :
    QuantumOrderedLabelPipeline.subdivisionStep cut (N,n,table e (index q) xs w J) =
      (N,n+m,table (nextTerm e 4) (index (nextQubit q e))
        (QuantumOrderedSubdivision.outputSites xs cut)
        (QuantumOrderedSubdivision.outputWord xs cut w)
        (QuantumOrderedSubdivision.outputCoefficient J N)) := by
  apply congrArg (Prod.mk N)
  exact value_table q e xs w J N _ _ _ _
    (subdivision_tag (index q) (fun a => n+(e.symm a).val) xs w hx cut)

theorem third_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 3) (hx : ∀ a, (xs a).Nodup) (N : ℕ) :
    QuantumOrderedLabelPipeline.thirdStep (N,n,table e (index q) xs w J) =
      (N,n+m,table (nextTerm e 7) (index (nextQubit q e))
        (QuantumOrderedThird.outputSites xs w) (QuantumOrderedThird.outputWord xs w)
        (QuantumOrderedThird.outputCoefficient J N)) := by
  apply congrArg (Prod.mk N)
  exact value_table q e xs w J N _ _ _ _
    (thirdBlock_tag (index q) (fun a => n+(e.symm a).val) xs w hlen hx)

omit [Fintype ι] in
theorem yy_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hx : ∀ a, (xs a).Nodup) (N : ℕ) :
    QuantumOrderedLabelPipeline.yyStep (N,n,table e (index q) xs w J) =
      (N,n+m,table (nextTerm e 4) (index (nextQubit q e))
        (QuantumOrderedYY.outputSites xs) (QuantumOrderedYY.outputWord xs w)
        (QuantumOrderedYY.outputCoefficient J N)) := by
  apply congrArg (Prod.mk N)
  exact value_table q e xs w J N _ _ _ _
    (yyBlock_tag (index q) (fun a => n+(e.symm a).val) xs w hx)

omit [Fintype ι] in
theorem private_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) (N : ℕ) :
    QuantumOrderedLabelPipeline.privateStep (N,n,table e (index q) xs w J) =
      (N,n+m,table (nextTerm e 4) (index (nextQubit q e))
        (QuantumOrderedPrivate.outputSites xs) (QuantumOrderedPrivate.outputWord xs w)
        (QuantumOrderedPrivate.outputCoefficient J N)) := by
  apply congrArg (Prod.mk N)
  exact value_table q e xs w J N _ _ _ _
    (privateBlock_tag (index q) (fun a => n+(e.symm a).val) xs w)

end ContinuumCoulomb.QuantumOrderedLabelTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete literal sparse-label compiler equals the actual ordered
six-to-four-to-three-to-two-to-XZ construction and private-pair stage. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelTable
open scoped Classical

variable {ι κ : Type} {m n : ℕ}

def terms1 (e : Fin m ≃ κ) := nextTerm e 4
def terms2 (e : Fin m ≃ κ) := nextTerm (terms1 e) 4
def terms3 (e : Fin m ≃ κ) := nextTerm (terms2 e) 7
def terms4 (e : Fin m ≃ κ) := nextTerm (terms3 e) 4
def terms5 (e : Fin m ≃ κ) := nextTerm (terms4 e) 7
def terms6 (e : Fin m ≃ κ) := nextTerm (terms5 e) 4

def qubits1 (q : Fin n ≃ ι) (e : Fin m ≃ κ) := nextQubit q e
def qubits2 (q : Fin n ≃ ι) (e : Fin m ≃ κ) := nextQubit (qubits1 q e) (terms1 e)
def qubits3 (q : Fin n ≃ ι) (e : Fin m ≃ κ) := nextQubit (qubits2 q e) (terms2 e)
def qubits4 (q : Fin n ≃ ι) (e : Fin m ≃ κ) := nextQubit (qubits3 q e) (terms3 e)
def qubits5 (q : Fin n ≃ ι) (e : Fin m ≃ κ) := nextQubit (qubits4 q e) (terms4 e)
def qubits6 (q : Fin n ≃ ι) (e : Fin m ≃ κ) := nextQubit (qubits5 q e) (terms5 e)

def finalCount (n m : ℕ) : ℕ :=
  n+m+m*4+m*4*4+m*4*4*7+m*4*4*7*4+m*4*4*7*4*7

theorem finalCount_eq (n m : ℕ) : finalCount n m=n+3717*m := by
  unfold finalCount
  omega

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem output_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hx : ∀ a, (xs a).Nodup) (N : ℕ) :
    QuantumOrderedLabelPipeline.output (N,n,table e (index q) xs w J) =
      (finalCount n m,table (terms6 e) (index (qubits6 q e))
        (QuantumOrderedPrivate.outputSites (QuantumOrderedXZ.sites xs w))
        (QuantumOrderedPrivate.outputWord (QuantumOrderedXZ.sites xs w)
          (QuantumOrderedXZ.word xs w))
        (QuantumOrderedPrivate.outputCoefficient (QuantumOrderedXZ.coefficient J N) N)) := by
  have h1 := subdivision_table q e xs w J hx N 3
  have h2 := subdivision_table (qubits1 q e) (terms1 e)
    (QuantumOrderedSubdivision.outputSites xs 3)
    (QuantumOrderedSubdivision.outputWord xs 3 w)
    (QuantumOrderedSubdivision.outputCoefficient J N)
    (QuantumOrderedSubdivision.outputSites_nodup xs 3 hx) N 2
  have h3 := third_table (qubits2 q e) (terms2 e)
    (QuantumOrderedXZ.threeSites xs) (QuantumOrderedXZ.threeWord xs w)
    (QuantumOrderedXZ.threeCoefficient J N)
    (QuantumOrderedXZ.threeSites_length xs hlen) (QuantumOrderedXZ.threeSites_nodup xs hx) N
  have h4 := yy_table (qubits3 q e) (terms3 e)
    (QuantumOrderedXZ.twoSites xs w) (QuantumOrderedXZ.twoWord xs w)
    (QuantumOrderedXZ.twoCoefficient J N)
    (QuantumOrderedXZ.twoSites_nodup xs w hlen hx) N
  have h5 := third_table (qubits4 q e) (terms4 e)
    (QuantumOrderedXZ.xzThreeSites xs w) (QuantumOrderedXZ.xzThreeWord xs w)
    (QuantumOrderedXZ.xzThreeCoefficient J N)
    (QuantumOrderedXZ.xzThreeSites_length xs w hlen)
    (QuantumOrderedXZ.xzThreeSites_nodup xs w hlen hx) N
  have h6 := private_table (qubits5 q e) (terms5 e)
    (QuantumOrderedXZ.sites xs w) (QuantumOrderedXZ.word xs w)
    (QuantumOrderedXZ.coefficient J N) N
  change _ = (N,n+m,table (terms1 e) (index (qubits1 q e))
    (QuantumOrderedSubdivision.outputSites xs 3)
    (QuantumOrderedSubdivision.outputWord xs 3 w)
    (QuantumOrderedSubdivision.outputCoefficient J N)) at h1
  change _ = (N,n+m+m*4,table (terms2 e) (index (qubits2 q e))
    (QuantumOrderedXZ.threeSites xs) (QuantumOrderedXZ.threeWord xs w)
    (QuantumOrderedXZ.threeCoefficient J N)) at h2
  change _ = (N,n+m+m*4+m*4*4,table (terms3 e) (index (qubits3 q e))
    (QuantumOrderedXZ.twoSites xs w) (QuantumOrderedXZ.twoWord xs w)
    (QuantumOrderedXZ.twoCoefficient J N)) at h3
  change _ = (N,n+m+m*4+m*4*4+m*4*4*7,table (terms4 e) (index (qubits4 q e))
    (QuantumOrderedXZ.xzThreeSites xs w) (QuantumOrderedXZ.xzThreeWord xs w)
    (QuantumOrderedXZ.xzThreeCoefficient J N)) at h4
  change _ = (N,n+m+m*4+m*4*4+m*4*4*7+m*4*4*7*4,
    table (terms5 e) (index (qubits5 q e))
    (QuantumOrderedXZ.sites xs w) (QuantumOrderedXZ.word xs w)
    (QuantumOrderedXZ.coefficient J N)) at h5
  unfold QuantumOrderedLabelPipeline.output
  rw [h1,h2,h3,h4,h5,h6]
  rfl

end ContinuumCoulomb.QuantumOrderedLabelTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumXZSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sampled rational exchange Hamiltonian approximates the entire logical X/Z family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

def rationalInputSize (J : κ → ℚ) : ℚ := Fintype.card κ+∑ e, |J e|
def rationalBudget (J : κ → ℚ) : ℚ := 1+2000000*rationalInputSize J+(7056*rationalInputSize J)^2
def rationalPenalty (N : ℕ) (J : κ → ℚ) : ℚ := 9*(rationalBudget J)^3*N

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSamplePrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic precision, computed from binary numerators, suffices for the physical error budget. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram

def precision (q : ℚ) (N : ℕ) : ℕ := q.num.natAbs.size+N.size

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSampleAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact termwise assembly of the computed physical exchange list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical

abbrev TypedBond (m : ℕ) := Fin m × (Fin m × ℚ)

def penaltyBonds (n : ℕ) (r : ℚ) : List (TypedBond (n*4)) :=
  List.ofFn fun e : Fin (n*6) =>
    let ik := (finProdFinEquiv : Fin n × Fin 6 ≃ Fin (n*6)).symm e
    (finProdFinEquiv (ik.1,qmaFourEdgeLeft ik.2),
      finProdFinEquiv (ik.1,qmaFourEdgeRight ik.2),r^2)

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal raw edge instructions encode the proved physical matrix. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample
open scoped BigOperators Classical

theorem penaltyBonds_distinct (n : ℕ) (r : ℚ) (b : TypedBond (n*4))
    (hb : b ∈ penaltyBonds n r) : b.1 ≠ b.2.1 := by
  obtain ⟨e,he⟩ := List.mem_ofFn.mp hb
  subst b
  intro h
  exact qmaFourEdge_distinct _ (congrArg Prod.snd (finProdFinEquiv.injective h))

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSampleBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A computable budget uses only the qubit count, term count and coefficient mass. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical

def universalErrorBudget (n m : ℕ) (r S : ℚ) : ℚ :=
  3*(6*n+25*m)*(1568*|r| *(1+(m+S))+26064*(m+S))+320800*S

variable {n : ℕ} {κ : Type*} [Fintype κ]

def boundedPrecision (N : ℕ) (_t : κ → QMAXZTerm n) (J : κ → ℚ) : ℕ :=
  precision (universalErrorBudget n (Fintype.card κ) (rationalPenalty N J) (∑ e, |J e|)) N

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawFamilyCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact correspondence between the emitted raw family and its certified finite Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample
open scoped BigOperators Classical

def packed {n m : ℕ} (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) : List Raw :=
  List.ofFn (fun e => pack (t e) (J e))

end ContinuumCoulomb.QuantumRawExchange

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
open QuantumAxisSample ExactQuantumFactoring.BitStackProgram

def mass (xs : List Raw) : ℚ := (xs.map (fun t => |t.2.2.2|)).sum
def size (xs : List Raw) : ℚ := xs.length+mass xs
def budget (xs : List Raw) : ℚ := 1+2000000*size xs+(7056*size xs)^2
def scale (N : ℕ) (xs : List Raw) : ℚ := 9*(budget xs)^3*N

abbrev ScheduleInput := ℕ × (ℕ × List Raw)

def errorBound (x : ScheduleInput) : ℚ :=
  universalErrorBudget x.1 x.2.2.length (scale x.2.1 x.2.2) (mass x.2.2)
def bits (x : ScheduleInput) : ℕ := QuantumAxisSample.precision (errorBound x) x.2.1
def scheduled (x : ScheduleInput) : FullInput := (x.1,(bits x,scale x.2.1 x.2.2),x.2.2)

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedRawBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The existing literal rational four-spin compiler applied to the actual
ordered X/Z words. Its input list preserves term and endpoint order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedRawBlock
open scoped BigOperators Classical

def terms {n m : ℕ} (xs : Fin m → List (Fin n)) (w : Fin m → Fin n → Fin 4) :
    Fin m → QMAXZTerm n := fun e => QuantumOrderedXZTerm.ofSites (xs e) (w e)

end ContinuumCoulomb.QuantumOrderedRawBlock

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conversion of the actual ordered sparse labels into the literal raw
X/Z instructions, including the explicit finite relabeling of their energy. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelTable
open scoped BigOperators Classical

variable {ι κ : Type} {n m : ℕ}

def numberedSites (q : Fin n ≃ ι) (e : Fin m ≃ κ) (xs : κ → List ι) :
    Fin m → List (Fin n) := fun a => (xs (e a)).map q.symm

def numberedWord (q : Fin n ≃ ι) (e : Fin m ≃ κ) (w : κ → ι → Fin 4) :
    Fin m → Fin n → Fin 4 := fun a i => w (e a) (q i)

theorem tag_numbered (q : Fin n ≃ ι) (xs : List ι) (w : ι → Fin 4) :
    QuantumOrderedLabelData.tag (index q) xs w =
      ((xs.map q.symm).map (fun i => (i.val,(w (q i)).val))) := by
  simp only [QuantumOrderedLabelData.tag,List.map_map,Function.comp_def,
    Equiv.apply_symm_apply,index]

end ContinuumCoulomb.QuantumOrderedLabelTable

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

abbrev Input := QuantumOrderedLabelFamily.Input

def qubitCount (x : Input) : ℕ := 4*(QuantumOrderedLabelPipeline.output x).1

def classify (xs : List Entry) : List QuantumRawExchange.Raw :=
  xs.map QuantumOrderedRawPacking.value

def labelEntries (x : Input) : List Entry := (QuantumOrderedLabelPipeline.output x).2

def rawEntries : Input → List QuantumRawExchange.Raw := classify ∘ labelEntries

def outputCount : Input → ℕ := Prod.fst ∘ QuantumOrderedLabelPipeline.output

def rawInput (x : Input) : QuantumRawExchange.ScheduleInput :=
  (outputCount x,x.1,rawEntries x)

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {m n : ℕ}

def finalSites (xs : κ → List ι) (w : κ → ι → Fin 4) :=
  QuantumOrderedPrivate.outputSites (QuantumOrderedXZ.sites xs w)

def finalWord (xs : κ → List ι) (w : κ → ι → Fin 4) :=
  QuantumOrderedPrivate.outputWord (QuantumOrderedXZ.sites xs w) (QuantumOrderedXZ.word xs w)

def finalCoefficient (J : κ → ℚ) (N : ℕ) :=
  QuantumOrderedPrivate.outputCoefficient (QuantumOrderedXZ.coefficient J N) N

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem qubitCount_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) (N : ℕ) :
    qubitCount (N,n,table e (index q) xs w J)=4*(n+3717*m) := by
  rw [qubitCount,QuantumOrderedLabelPipeline.output_qubits]
  simp only [table,List.length_ofFn]

end ContinuumCoulomb.QuantumOrderedLabelCompile

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedWeightBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial envelopes for the literal four- and seven-word gadgets.
Only the term count, input coefficient bound and unary precision enter these
envelopes.  No bound on the Hilbert-space dimension is used. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedXZ
open scoped BigOperators Classical

def weightEnvelope (R B : ℚ) : ℚ :=
  R^3+R^2*B+R^2+R*(1+B^2)+1+B^2

def scaleEnvelope (m : ℕ) (B : ℚ) (N : ℕ) : ℚ :=
  8*(4*(1+(m:ℚ)*(1+B)^2))^4*N

def stepEnvelope (m : ℕ) (B : ℚ) (N : ℕ) : ℚ := weightEnvelope (scaleEnvelope m B N) B

variable {κ : Type} [Fintype κ]

/-- A fixed fivefold composition of explicit polynomials. -/
def pipelineBound (m : ℕ) (B : ℚ) (N : ℕ) : ℕ → ℚ
  | 0 => B
  | k+1 => stepEnvelope (3136*m) (pipelineBound m B N k) N

end ContinuumCoulomb.QuantumOrderedXZ

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedFinalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An integer polynomial bound for the complete six-stage ordered compiler,
including the private-pair subdivision before the physical four-spin step. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedXZ
open scoped Classical

def weightNat (R B : ℕ) : ℕ := R^3+R^2*B+R^2+R*(1+B^2)+1+B^2
def scaleNat (m B N : ℕ) : ℕ := 8*(4*(1+m*(1+B)^2))^4*N
def stepNat (m B N : ℕ) : ℕ := weightNat (scaleNat m B N) B
def pipelineNat (m B N : ℕ) : ℕ → ℕ
  | 0 => B
  | k+1 => stepNat (3136*m) (pipelineNat m B N k) N

end ContinuumCoulomb.QuantumOrderedXZ

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawOutputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial magnitude envelopes for every actual physical edge and scalar
offset in the rational four-spin output. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample

def outputBound (n m : ℕ) (R B : ℝ) : ℝ :=
  (6*n+1)*R^2+3920*R*(1+B)+(685600*m+26000)*B+1

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A natural polynomial envelope for the actual rational raw compiler.
Only the raw term count, coefficient magnitude and unary precision enter it. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange

def budgetNat (m B : ℕ) : ℕ := 1+2000000*(m+m*B)+(7056*(m+m*B))^2
def scaleNat (m B N : ℕ) : ℕ := 9*(budgetNat m B)^3*N
def outputNat (n m B N : ℕ) : ℕ :=
  let R := scaleNat m B N
  (6*n+1)*R^2+3920*R*(1+B)+(685600*m+26000)*B+1

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCoefficientEnvelopeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal unary programs for the logical and physical coefficient bounds.
The only arguments are qubit count, term count, initial magnitude and precision. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCoefficientEnvelopeProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Input := QuantumCoefficientPrograms.LatticeInput
def value (x : Input) : ℕ := QuantumRawExchange.outputNat
  (x.1+3717*x.2.1) (12544*x.2.1)
  (QuantumOrderedXZ.pipelineNat x.2.1 x.2.2.1 x.2.2.2 6) x.2.2.2

end ContinuumCoulomb.QuantumCoefficientEnvelopeProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFiniteMembership
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal membership tests for the finite geometry tables used by the
140-candidate planar route selector. The Boolean fold has constant-size state. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFiniteMembership
open ExactQuantumFactoring.BitStackProgram

theorem fold_or (xs : List Bool) (b : Bool) :
    xs.foldl (fun c a => a || c) b = (xs.any id || b) := by
  induction xs generalizing b with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons,List.any_cons]
    rw [ih]
    cases a <;> cases b <;> simp

end ContinuumCoulomb.QuantumFiniteMembership

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
open ExactQuantumFactoring.BitStackProgram

theorem filter_eq_flatten {α : Type} (p : α → Bool) (xs : List α) :
    (xs.map (fun a => if p a then [a] else [])).flatten = xs.filter p := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons,List.flatten_cons,List.filter_cons,ih]
    cases p a <;> simp

end ContinuumCoulomb.QuantumRoutingTable

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
open ExactQuantumFactoring.BitStackProgram

abbrev Parameters := ℕ × (Bool × ℚ)

end ContinuumCoulomb.QuantumListPathProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingListBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nine ordinary exchange interactions in a crossing gadget, serialized
in a fixed order. Every endpoint and rational coefficient is computed literally. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListBlock
open ExactQuantumFactoring.BitStackProgram

abbrev Sites := (ℕ × ℕ) × (ℕ × ℕ)
def site (s : Sites) : Fin 4 → ℕ := ![s.1.1,s.1.2,s.2.1,s.2.2]
abbrev Crossing := (ℚ × ℚ) × Sites
abbrev Parameters := ℕ × ℚ
abbrev Input := Parameters × (ℕ × Crossing)

def base (x : Input) : ℕ := x.1.1+2*x.2.1

def left (x : Input) : Fin 9 → ℕ :=
  ![site x.2.2.2 0,site x.2.2.2 0,site x.2.2.2 1,site x.2.2.2 2,
    base x,site x.2.2.2 0,site x.2.2.2 1,site x.2.2.2 2,site x.2.2.2 3]
def right (x : Input) : Fin 9 → ℕ :=
  ![site x.2.2.2 1,site x.2.2.2 3,site x.2.2.2 2,site x.2.2.2 3,
    base x+1,base x,base x,base x+1,base x+1]
def coefficient (x : Input) : Fin 9 → ℚ :=
  let c := QuantumRoutingCode.coefficients (x.1.2,x.2.2.1)
  ![c 5,c 6,c 7,c 8,x.1.2^2,c 1,c 2,c 3,c 4]

end ContinuumCoulomb.QuantumCrossingListBlock

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingListFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal simultaneous crossing layer: nine bonds and two fresh spins per
crossing, with every scalar correction retained. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListBlock
open ExactQuantumFactoring.BitStackProgram

abbrev FamilyInput := Parameters × List Crossing
def zeroCrossing : Crossing := ((0,0),(0,0),(0,0))
def indexed (x : ℕ × FamilyInput) : Input :=
  (x.2.1,x.1,(x.2.2.drop x.1).headD zeroCrossing)
def offset (x : Input) : ℚ := QuantumRoutingCode.coefficients (x.1.2,x.2.2.1) 9
def familyOffset (x : FamilyInput) : ℚ := (x.2.map (fun c => offset (x.1,0,c))).sum

theorem indexed_mem (x : FamilyInput) (i : ℕ) (hi : i<x.2.length) :
    (indexed (i,x)).2.2 ∈ x.2 := by
  change ((x.2.drop i).headD zeroCrossing) ∈ x.2
  rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

end ContinuumCoulomb.QuantumCrossingListBlock

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingScaleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational scale for a simultaneous crossing layer, computed from
its retained coefficients and the two crossing coefficients at each cell. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingScaleProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators Classical

abbrev Pair := ℚ × ℚ
abbrev Input := (ℚ × ℚ) × (List ℚ × List Pair)
def linearCost (p : Pair) : ℚ := 1+|p.1|+|p.2|
def squareCost (p : Pair) : ℚ := (linearCost p)^2
def base (x : Input) : ℚ := 3*(x.2.1.map abs).sum+|x.1.2|
def active (x : Input) : ℚ := 6*(x.2.2.map linearCost).sum
def correction (x : Input) : ℚ := base x+12*(x.2.2.map squareCost).sum
def value (x : Input) : ℚ :=
  16*(active x+correction x+1)^3*x.1.1+4*(active x+correction x+1)+1

end ContinuumCoulomb.QuantumCrossingScaleProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSelectCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite endpoint scans recover the actual selected rational couplings.
No matrix or energy comparison is assumed by this source-data bridge. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open QuantumCrossingListBlock
open scoped BigOperators Classical

def encodedSites {n r : ℕ} (site : Fin r → Fin 4 → Fin n) (i : Fin r) : Sites :=
  (((site i 0).val,(site i 1).val),((site i 2).val,(site i 3).val))

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWalkErasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coarse route's library loop erasure is the explicit right-to-left
finite-list algorithm. This identifies the actual path data needed by the
literal spatial compiler. -/

noncomputable section
open scoped List
namespace ContinuumCoulomb
namespace QuantumWalkErasure
open ExactQuantumFactoring.BitStackProgram

variable {α : Type} [DecidableEq α]

def step (a : α) (xs : List α) : List α :=
  if a ∈ xs then xs.drop (xs.idxOf a) else a::xs

def erase (xs : List α) : List α := xs.foldr step []

@[simp] theorem erase_nil : erase ([] : List α) = [] := rfl
@[simp] theorem erase_cons (a : α) (xs : List α) : erase (a::xs) = step a (erase xs) := rfl

theorem step_sublist (a : α) (xs : List α) : step a xs <+ a::xs := by
  unfold step
  split
  · exact (List.drop_sublist _ _).trans (List.sublist_cons_self _ _)
  · exact List.Sublist.refl _

end QuantumWalkErasure

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEndpointListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The endpoint arm list is computed from its ordinal port, lane color and
coarse vertex. All three quantities are supplied by the explicit slot and
incident-rank programs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEndpointListProgram
open ExactQuantumFactoring.BitStackProgram

abbrev ArmInput := ℕ × ℕ

end ContinuumCoulomb.QuantumEndpointListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary spin edges and polynomial full-space error for a parallel fork round. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ν : Type*} [Fintype ν]

def qmaForksBaseLeft {n r : ℕ} (left : ν → Fin n) (site : Fin r → Fin 3 → Fin n) :
    ν ⊕ Fin r → Fin n := Sum.elim left (fun e => site e 1)
def qmaForksBaseRight {n r : ℕ} (right : ν → Fin n) (site : Fin r → Fin 3 → Fin n) :
    ν ⊕ Fin r → Fin n := Sum.elim right (fun e => site e 2)

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
open scoped BigOperators Classical
variable {ν : Type*} [Fintype ν]

def qmaForkOuter {n r : ℕ} (site : Fin r → Fin 3 → Fin n) (p : Fin r × Fin 2) : Fin n :=
  site p.1 (if p.2 = 0 then 1 else 2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkDegrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The parallel fork graph halves the degree of its center. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

/-- A constant degree bound permits a constant number of fork rounds. -/
def qmaForkDegreeAfter (d : ℕ) : ℕ → ℕ
  | 0 => d
  | k+1 => qmaForkDegreeAfter d k / 2 + qmaForkDegreeAfter d k % 2

theorem qmaForkDegreeAfter_bound (d k : ℕ) :
    qmaForkDegreeAfter d k ≤ max 1 (d-k) := by
  induction k with
  | zero => simp [qmaForkDegreeAfter]
  | succ k ih =>
    simp only [qmaForkDegreeAfter]
    by_cases h : qmaForkDegreeAfter d k ≤ 1
    · have hf : qmaForkDegreeAfter d k / 2 + qmaForkDegreeAfter d k % 2 ≤ 1 := by omega
      exact hf.trans (le_max_left _ _)
    · have hf : qmaForkDegreeAfter d k / 2 + qmaForkDegreeAfter d k % 2 <
          qmaForkDegreeAfter d k := by omega
      omega

theorem qmaForkDegreeAfter_constant (d D : ℕ) (hd : d ≤ D) :
    qmaForkDegreeAfter d D ≤ 1 := by
  have h := qmaForkDegreeAfter_bound d D
  simpa [Nat.sub_eq_zero_of_le hd] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Odd subdivision gives every original incidence its own private fork port. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaOriginalEndpoint {n m : ℕ} (left right : Fin m → Fin n) (p : Fin m × Fin 2) : Fin n :=
  if p.2 = 0 then left p.1 else right p.1

def qmaOriginalPortCount {n m : ℕ} (left right : Fin m → Fin n) (i : Fin n) : ℕ :=
  Fintype.card {p : Fin m × Fin 2 // qmaOriginalEndpoint left right p = i}

def qmaOriginalPortEquiv {n m : ℕ} (left right : Fin m → Fin n) :
    (Σ i, Fin (qmaOriginalPortCount left right i)) ≃ Fin m × Fin 2 :=
  (Equiv.sigmaCongrRight (fun i => (Fintype.equivFin
    {p : Fin m × Fin 2 // qmaOriginalEndpoint left right p = i}).symm)).trans
      (Equiv.sigmaFiberEquiv (qmaOriginalEndpoint left right))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered rational data for the degree-three fork compiler. Original centers
retain their numbers. Each pair of active ports receives two consecutive new
spin numbers, and an unpaired port remains active at its original center. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList

abbrev Port := ℕ × ℚ
abbrev Pair := Port × Port
abbrev Groups := List (List Port)
abbrev TaggedPair := ℕ × Pair

def portAt (ps : List Port) (i : ℕ) : Port := (ps.drop i).headD (0,0)
def groupAt (gs : Groups) (i : ℕ) : List Port := (gs.drop i).headD []

def pairs (ps : List Port) : List Pair :=
  (List.range (ps.length/2)).map (fun i => (portAt ps (2*i),portAt ps (2*i+1)))

def unpaired (ps : List Port) : List Port := ps.drop (2*(ps.length/2))

def catalog (gs : Groups) : List TaggedPair :=
  ((List.range gs.length).map (fun i => (pairs (groupAt gs i)).map (fun p => (i,p)))).flatten

def pairCount (gs : Groups) : ℕ := (gs.map (fun ps => ps.length/2)).sum
def pairStart (gs : Groups) (i : ℕ) : ℕ := pairCount (gs.take i)

def pairLinear (p : Pair) : ℚ := 1+2*|p.1.2|+2*|p.2.2|
def pairSquare (p : Pair) : ℚ := (1+|p.1.2|+|p.2.2|)^2
def pairOffset (p : Pair) : ℚ := 3/4+3*p.1.2^2+3*p.2.2^2

def nextGroup (n : ℕ) (R : ℚ) (gs : Groups) (i : ℕ) : List Port :=
  let ps := groupAt gs i
  (List.range (ps.length/2)).map (fun j => (n+2*(pairStart gs i+j),R)) ++ unpaired ps

theorem pairs_length (ps : List Port) : (pairs ps).length=ps.length/2 := by
  simp [pairs]

theorem unpaired_length (ps : List Port) : (unpaired ps).length=ps.length%2 := by
  simp only [unpaired,List.length_drop]
  omega

theorem pairCount_cons (ps : List Port) (gs : Groups) :
    pairCount (ps::gs)=ps.length/2+pairCount gs := rfl

theorem groupAt_cons_zero (ps : List Port) (gs : Groups) : groupAt (ps::gs) 0=ps := rfl

theorem groupAt_cons_succ (ps : List Port) (gs : Groups) (i : ℕ) :
    groupAt (ps::gs) (i+1)=groupAt gs i := by
  simp [groupAt,List.drop_succ_cons]

theorem nextGroup_length (n : ℕ) (R : ℚ) (gs : Groups) (i : ℕ) :
    (nextGroup n R gs i).length=(groupAt gs i).length/2+(groupAt gs i).length%2 := by
  simp [nextGroup,unpaired_length]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adjacent pairing partitions the actual port lists without reordering or
dropping the odd final port. These identities connect the list compiler to the
full active-star Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList

theorem catalog_cons (ps : List Port) (gs : Groups) :
    catalog (ps::gs) = (pairs ps).map (fun p => (0,p)) ++
      (catalog gs).map (fun p => (p.1+1,p.2)) := by
  unfold catalog
  simp only [List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,
    List.flatten_cons,groupAt_cons_zero,Function.comp_def,groupAt_cons_succ]
  rw [List.map_flatten,List.map_map]
  simp only [List.map_map,Function.comp_def]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite bond packet emitted for parallel forks has the exact full-space
Hamiltonian used in the calibrated perturbation estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open QuantumRawExchange QuantumAxisSample
open scoped BigOperators Classical

def graphConstant {r : ℕ} (c R : ℚ) (J K : Fin r → ℚ) : ℚ :=
  (c+∑ e, (3/4+3*(J e)^2+3*(K e)^2))+3*r*R^2

def graphScale {r m : ℕ} (w : Fin m → ℚ) (J K : Fin r → ℚ) (c N : ℚ) : ℚ :=
  let B := 3*(∑ a, |w a|)+|c|
  let A := 3*∑ e, (1+2*|J e|+2*|K e|)
  let D := B+12*∑ e, (1+|J e|+|K e|)^2
  16*(A+D+1)^3*N+4*(A+D+1)+1

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compiler's prefix sums enumerate precisely the actual pairs. The
result fixes which two fresh spins belong to each center and local pair. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList

theorem pairStart_zero (gs : Groups) : pairStart gs 0=0 := rfl

theorem pairStart_cons_succ (ps : List Port) (gs : Groups) (i : ℕ) :
    pairStart (ps::gs) (i+1)=ps.length/2+pairStart gs i := by
  simp only [pairStart,List.take_succ_cons,pairCount_cons]

theorem pairStart_bound (gs : Groups) (i : ℕ) (hi : i < gs.length) :
    pairStart gs i+(groupAt gs i).length/2 ≤ pairCount gs := by
  induction gs generalizing i with
  | nil => simp at hi
  | cons ps gs ih =>
    cases i with
    | zero => simp only [pairStart_zero,zero_add,groupAt_cons_zero,pairCount_cons]; omega
    | succ i =>
      have hi' : i < gs.length := by simpa using hi
      rw [pairStart_cons_succ,groupAt_cons_succ,pairCount_cons]
      have := ih i hi'
      omega

theorem pair_index_lt (gs : Groups) (i j : ℕ) (hi : i < gs.length)
    (hj : j < (groupAt gs i).length/2) : pairStart gs i+j < pairCount gs := by
  have := pairStart_bound gs i hi
  omega

theorem pairs_getElem? (ps : List Port) (j : ℕ) (hj : j < ps.length/2) :
    (pairs ps)[j]?=some (portAt ps (2*j),portAt ps (2*j+1)) := by
  rw [List.getElem?_eq_getElem (by simpa only [pairs_length] using hj)]
  simp only [pairs,List.getElem_map,List.getElem_range]

theorem catalog_getElem? (gs : Groups) (i j : ℕ) (hi : i < gs.length)
    (hj : j < (groupAt gs i).length/2) :
    (catalog gs)[pairStart gs i+j]? =
      some (i,(portAt (groupAt gs i) (2*j),portAt (groupAt gs i) (2*j+1))) := by
  induction gs generalizing i with
  | nil => simp at hi
  | cons ps gs ih =>
    cases i with
    | zero =>
      rw [catalog_cons,pairStart_zero,zero_add,
        List.getElem?_append_left (by simpa only [List.length_map,pairs_length,
          groupAt_cons_zero] using hj),List.getElem?_map]
      rw [groupAt_cons_zero] at hj ⊢
      rw [pairs_getElem? ps j hj]
      rfl
    | succ i =>
      have hi' : i < gs.length := by simpa using hi
      rw [groupAt_cons_succ] at hj ⊢
      rw [catalog_cons,pairStart_cons_succ,
        List.getElem?_append_right (by simp only [List.length_map,pairs_length]; omega),
        List.length_map,pairs_length]
      have he : ps.length/2+pairStart gs i+j-ps.length/2=pairStart gs i+j := by omega
      rw [he,List.getElem?_map,ih i hi' hj]
      rfl

theorem catalog_headD (gs : Groups) (i j : ℕ) (hi : i < gs.length)
    (hj : j < (groupAt gs i).length/2) :
    ((catalog gs).drop (pairStart gs i+j)).headD (0,((0,0),(0,0))) =
      (i,(portAt (groupAt gs i) (2*j),portAt (groupAt gs i) (2*j+1))) := by
  rw [List.headD_eq_head?_getD,List.head?_drop,catalog_getElem? gs i j hi hj]
  rfl

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListOrdinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit prefix index is a bijection between center-local pairs and
the consecutive mediator numbers used by the literal compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped BigOperators Classical

abbrev LocalPair (gs : Groups) := Σ i : Fin gs.length, Fin ((groupAt gs i.val).length/2)

def pairIndex (gs : Groups) (p : LocalPair gs) : Fin (pairCount gs) :=
  ⟨pairStart gs p.1.val+p.2.val,pair_index_lt gs p.1.val p.2.val p.1.isLt p.2.isLt⟩

theorem pairIndex_injective (gs : Groups) : Function.Injective (pairIndex gs) := by
  intro p q h
  have hp := catalog_getElem? gs p.1.val p.2.val p.1.isLt p.2.isLt
  have hq := catalog_getElem? gs q.1.val q.2.val q.1.isLt q.2.isLt
  have hn : pairStart gs p.1.val+p.2.val=pairStart gs q.1.val+q.2.val := congrArg Fin.val h
  rw [hn,hq] at hp
  have hc : p.1=q.1 := Fin.ext (congrArg Prod.fst (Option.some.inj hp)).symm
  rcases p with ⟨i,j⟩
  rcases q with ⟨k,l⟩
  dsimp only at hc
  subst k
  have hj : j=l := Fin.ext (by dsimp only at hn; omega)
  subst l
  rfl

theorem localPair_card (gs : Groups) : Fintype.card (LocalPair gs)=pairCount gs := by
  simp only [LocalPair,Fintype.card_sigma,Fintype.card_fin]
  have hlist : List.ofFn (fun i : Fin gs.length => (groupAt gs i.val).length/2) =
      gs.map (fun ps => ps.length/2) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hi' : i < gs.length := by simpa only [List.length_ofFn] using hi
      simp only [List.getElem_ofFn,List.getElem_map,groupAt,List.headD_eq_head?_getD,
        List.head?_drop,List.getElem?_eq_getElem hi',Option.getD_some]
  rw [← List.sum_ofFn,hlist]
  rfl

def pairEquiv (gs : Groups) : LocalPair gs ≃ Fin (pairCount gs) :=
  Equiv.ofBijective (pairIndex gs) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨pairIndex_injective gs,by rw [Fintype.card_fin,localPair_card]⟩)

theorem pairEquiv_val (gs : Groups) (p : LocalPair gs) :
    (pairEquiv gs p).val=pairStart gs p.1.val+p.2.val := rfl

theorem catalog_pairEquiv (gs : Groups) (p : LocalPair gs) :
    ((catalog gs).drop (pairEquiv gs p).val).headD (0,((0,0),(0,0))) =
      (p.1.val,(portAt (groupAt gs p.1.val) (2*p.2.val),
        portAt (groupAt gs p.1.val) (2*p.2.val+1))) :=
  catalog_headD gs p.1.val p.2.val p.1.isLt p.2.isLt

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual fork sites obtained from the ordered port arrays. Their bounds and
injectivity are the geometric hypotheses of the parallel perturbation theorem. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList

structure ValidPorts (n : ℕ) (gs : Groups) : Prop where
  centers : gs.length ≤ n
  bounded : ∀ (i : Fin gs.length) (j : Fin (groupAt gs i.val).length),
    (portAt (groupAt gs i.val) j.val).1 < n
  disjoint : ∀ (i k : Fin gs.length) (j : Fin (groupAt gs k.val).length),
    i.val ≠ (portAt (groupAt gs k.val) j.val).1
  injective : ∀ (i k : Fin gs.length) (j : Fin (groupAt gs i.val).length)
    (l : Fin (groupAt gs k.val).length),
    (portAt (groupAt gs i.val) j.val).1=(portAt (groupAt gs k.val) l.val).1 →
      i=k ∧ j.val=l.val

def localPair (gs : Groups) (e : Fin (pairCount gs)) : LocalPair gs :=
  (pairEquiv gs).symm e

def localFirst (gs : Groups) (e : Fin (pairCount gs)) :
    Fin (groupAt gs (localPair gs e).1.val).length :=
  ⟨2*(localPair gs e).2.val,by have := (localPair gs e).2.isLt; omega⟩

def localSecond (gs : Groups) (e : Fin (pairCount gs)) :
    Fin (groupAt gs (localPair gs e).1.val).length :=
  ⟨2*(localPair gs e).2.val+1,by have := (localPair gs e).2.isLt; omega⟩

def actualSite {n : ℕ} {gs : Groups} (h : ValidPorts n gs) (e : Fin (pairCount gs)) :
    Fin 3 → Fin n :=
  ![⟨(localPair gs e).1.val,lt_of_lt_of_le (localPair gs e).1.isLt h.centers⟩,
    ⟨(portAt (groupAt gs (localPair gs e).1.val) (localFirst gs e).val).1,
      h.bounded (localPair gs e).1 (localFirst gs e)⟩,
    ⟨(portAt (groupAt gs (localPair gs e).1.val) (localSecond gs e).val).1,
      h.bounded (localPair gs e).1 (localSecond gs e)⟩]

def actualJ (gs : Groups) (e : Fin (pairCount gs)) : ℚ :=
  (portAt (groupAt gs (localPair gs e).1.val) (localFirst gs e).val).2

def actualK (gs : Groups) (e : Fin (pairCount gs)) : ℚ :=
  (portAt (groupAt gs (localPair gs e).1.val) (localSecond gs e).val).2

theorem actualSite_injective {n : ℕ} {gs : Groups} (h : ValidPorts n gs)
    (e : Fin (pairCount gs)) : Function.Injective (actualSite h e) := by
  intro a b hab
  have hh := congrArg Fin.val hab
  fin_cases a <;> fin_cases b <;> simp only [actualSite] at hh ⊢
  · exact (h.disjoint (localPair gs e).1 (localPair gs e).1 (localFirst gs e) hh).elim
  · exact (h.disjoint (localPair gs e).1 (localPair gs e).1 (localSecond gs e) hh).elim
  · exact (h.disjoint (localPair gs e).1 (localPair gs e).1 (localFirst gs e) hh.symm).elim
  · have hp := (h.injective (localPair gs e).1 (localPair gs e).1
      (localFirst gs e) (localSecond gs e) hh).2
    simp only [localFirst,localSecond] at hp
    omega
  · exact (h.disjoint (localPair gs e).1 (localPair gs e).1 (localSecond gs e) hh.symm).elim
  · have hp := (h.injective (localPair gs e).1 (localPair gs e).1
      (localSecond gs e) (localFirst gs e) hh).2
    simp only [localFirst,localSecond] at hp
    omega

theorem catalog_actualSite {n : ℕ} {gs : Groups} (h : ValidPorts n gs)
    (e : Fin (pairCount gs)) :
    ((catalog gs).drop e.val).headD (0,((0,0),(0,0))) =
      ((actualSite h e 0).val,((actualSite h e 1).val,actualJ gs e),
        ((actualSite h e 2).val,actualK gs e)) := by
  have hc := catalog_pairEquiv gs (localPair gs e)
  rw [show pairEquiv gs (localPair gs e)=e from (pairEquiv gs).apply_symm_apply e] at hc
  exact hc

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing the actual fresh-port list by its consecutive mediator number. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped BigOperators Classical

theorem range_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum=∑ i : Fin n, f i.val := by
  have h : List.ofFn (fun i : Fin n => f i.val)=(List.range n).map f := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
  rw [← h,List.sum_ofFn]

theorem next_groupAt (n : ℕ) (R : ℚ) (gs : Groups) (i : ℕ) (hi : i < gs.length) :
    groupAt ((List.range gs.length).map (nextGroup n R gs)) i=nextGroup n R gs i := by
  rw [groupAt,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem (by simpa using hi)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListNextPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact lookup formulas for fresh and retained active ports in the next
literal round. They expose the indices needed to preserve port separation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList

theorem portAt_eq_getElem (ps : List Port) (j : ℕ) (hj : j < ps.length) :
    portAt ps j=ps[j] := by
  simp only [portAt,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem hj,Option.getD_some]

theorem nextGroup_portAt_fresh (n : ℕ) (R : ℚ) (gs : Groups) (i j : ℕ)
    (hj : j < (groupAt gs i).length/2) :
    portAt (nextGroup n R gs i) j=(n+2*(pairStart gs i+j),R) := by
  simp only [portAt,nextGroup,List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_append_left (by simpa only [List.length_map,List.length_range] using hj),
    List.getElem?_eq_getElem (by simpa only [List.length_map,List.length_range] using hj)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range]

theorem nextGroup_portAt_retained (n : ℕ) (R : ℚ) (gs : Groups) (i j : ℕ)
    (hj : (groupAt gs i).length/2 ≤ j) :
    portAt (nextGroup n R gs i) j=
      portAt (groupAt gs i) (2*((groupAt gs i).length/2)+(j-(groupAt gs i).length/2)) := by
  simp only [portAt,nextGroup,List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_append_right (by simpa only [List.length_map,List.length_range] using hj)]
  simp only [List.length_map,List.length_range,unpaired,List.getElem?_drop]

theorem retained_index_lt (d j : ℕ) (hj : j < d/2+d%2) (hlarge : d/2 ≤ j) :
    2*(d/2)+(j-d/2) < d := by omega

theorem fresh_index_lt (gs : Groups) (i j : ℕ) (hi : i < gs.length)
    (hj : j < (groupAt gs i).length/2) :
    pairStart gs i+j < pairCount gs := pair_index_lt gs i j hi hj

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListNextValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every literal fork round keeps the active ports distinct from one another
and from the original centers. Fresh ports use the injective prefix index;
retained ports inherit the preceding round's separation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList

theorem nextGroup_bounded {n : ℕ} {gs : Groups} (h : ValidPorts n gs) (R : ℚ)
    (i j : ℕ) (hi : i < gs.length) (hj : j < (nextGroup n R gs i).length) :
    (portAt (nextGroup n R gs i) j).1 < n+2*pairCount gs := by
  rw [nextGroup_length] at hj
  by_cases hf : j < (groupAt gs i).length/2
  · rw [nextGroup_portAt_fresh n R gs i j hf]
    have := fresh_index_lt gs i j hi hf
    dsimp only
    omega
  · have ho := retained_index_lt (groupAt gs i).length j hj (by omega)
    rw [nextGroup_portAt_retained n R gs i j (by omega)]
    have := h.bounded ⟨i,hi⟩ ⟨_,ho⟩
    dsimp only at this
    omega

theorem nextGroup_disjoint {n : ℕ} {gs : Groups} (h : ValidPorts n gs) (R : ℚ)
    (k i j : ℕ) (hk : k < gs.length) (hi : i < gs.length)
    (hj : j < (nextGroup n R gs i).length) :
    k ≠ (portAt (nextGroup n R gs i) j).1 := by
  rw [nextGroup_length] at hj
  by_cases hf : j < (groupAt gs i).length/2
  · rw [nextGroup_portAt_fresh n R gs i j hf]
    have := h.centers
    dsimp only
    omega
  · have ho := retained_index_lt (groupAt gs i).length j hj (by omega)
    rw [nextGroup_portAt_retained n R gs i j (by omega)]
    exact h.disjoint ⟨k,hk⟩ ⟨i,hi⟩ ⟨_,ho⟩

theorem nextGroup_injective {n : ℕ} {gs : Groups} (h : ValidPorts n gs) (R : ℚ)
    (i k j l : ℕ) (hi : i < gs.length) (hk : k < gs.length)
    (hj : j < (nextGroup n R gs i).length)
    (hl : l < (nextGroup n R gs k).length)
    (he : (portAt (nextGroup n R gs i) j).1=
      (portAt (nextGroup n R gs k) l).1) : i=k ∧ j=l := by
  rw [nextGroup_length] at hj hl
  by_cases hf : j < (groupAt gs i).length/2
  · rw [nextGroup_portAt_fresh n R gs i j hf] at he
    by_cases hg : l < (groupAt gs k).length/2
    · rw [nextGroup_portAt_fresh n R gs k l hg] at he
      have hp : pairIndex gs ⟨⟨i,hi⟩,⟨j,hf⟩⟩=
          pairIndex gs ⟨⟨k,hk⟩,⟨l,hg⟩⟩ := by
        apply Fin.ext
        dsimp only [pairIndex]
        dsimp only at he
        omega
      have hv := congrArg (fun p : LocalPair gs => (p.1.val,p.2.val))
        (pairIndex_injective gs hp)
      exact Prod.mk.inj hv
    · have ho := retained_index_lt (groupAt gs k).length l hl (by omega)
      rw [nextGroup_portAt_retained n R gs k l (by omega)] at he
      have hb := h.bounded ⟨k,hk⟩ ⟨_,ho⟩
      dsimp only at he hb
      omega
  · have ho := retained_index_lt (groupAt gs i).length j hj (by omega)
    rw [nextGroup_portAt_retained n R gs i j (by omega)] at he
    by_cases hg : l < (groupAt gs k).length/2
    · rw [nextGroup_portAt_fresh n R gs k l hg] at he
      have hb := h.bounded ⟨i,hi⟩ ⟨_,ho⟩
      dsimp only at he hb
      omega
    · have hp := retained_index_lt (groupAt gs k).length l hl (by omega)
      rw [nextGroup_portAt_retained n R gs k l (by omega)] at he
      have hh := h.injective ⟨i,hi⟩ ⟨k,hk⟩ ⟨_,ho⟩ ⟨_,hp⟩ he
      have hik : i=k := congrArg Fin.val hh.1
      refine ⟨hik,?_⟩
      subst k
      dsimp only at hh
      omega

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The even and odd entries in the initial endpoint table are precisely
the two couplings belonging to each physical singlet. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped BigOperators Classical

def initialIndexEquiv (m : ℕ) : Fin m × Fin 2 ≃ Fin (2*m) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))

theorem initialIndexEquiv_val (m : ℕ) (e : Fin m) (b : Fin 2) :
    (initialIndexEquiv m (e,b)).val=2*e.val+b.val := by
  change b.val+2*e.val=2*e.val+b.val
  omega

theorem initial_evenodd_sum {M : Type*} [AddCommMonoid M] (m : ℕ) (f : ℕ → M) :
    ((List.range (2*m)).map f).sum=∑ e : Fin m, (f (2*e.val)+f (2*e.val+1)) := by
  rw [range_sum]
  have h := (initialIndexEquiv m).sum_comp (fun j => f j.val)
  simpa only [Fintype.sum_prod_type,Fin.sum_univ_two,initialIndexEquiv_val,
    Fin.val_zero,Fin.val_one,add_zero] using h.symm

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial emitted couplings are the simultaneous odd-path singlet
Hamiltonian used by the already proved full-space perturbation estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open QuantumRawExchange QuantumAxisSample
open scoped BigOperators Classical

def initialConstant {m : ℕ} (J : Fin m → ℚ) (c R : ℚ) : ℚ :=
  (c+∑ e, (3/4+3*(J e)^2))+3*m*R^2

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence counts for the literal ordinary-bond list. The four newly emitted
bonds have exactly the graph used by the physical fork degree estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped BigOperators Classical

def incident (v a b : ℕ) : ℕ := if a=v ∨ b=v then 1 else 0

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListOuter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Paired outer ports form an injective family. The explicit local-pair
numbering therefore meets the simultaneous-fork degree hypotheses. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped Classical

def outerPort (gs : Groups) (p : Fin (pairCount gs) × Fin 2) :
    Σ i : Fin gs.length, Fin (groupAt gs i.val).length :=
  ⟨(localPair gs p.1).1,
   ⟨2*(localPair gs p.1).2.val+p.2.val,by
      have := (localPair gs p.1).2.isLt
      have := p.2.isLt
      omega⟩⟩

theorem outerPort_injective (gs : Groups) : Function.Injective (outerPort gs) := by
  rintro ⟨e,b⟩ ⟨f,c⟩ h
  have hi : (localPair gs e).1=(localPair gs f).1 := congrArg (fun q : (Σ i : Fin gs.length, Fin (groupAt gs i.val).length) => q.1) h
  have hj : 2*(localPair gs e).2.val+b.val=2*(localPair gs f).2.val+c.val :=
    congrArg (fun p => p.2.val) h
  have hb := b.isLt
  have hc := c.isLt
  have heq : localPair gs e=localPair gs f := by
    apply Sigma.ext hi
    exact (Fin.heq_ext_iff (congrArg (fun i : Fin gs.length => (groupAt gs i.val).length/2) hi)).2 (by omega)
  have hef : e=f := (pairEquiv gs).symm.injective heq
  have hbc : b=c := Fin.ext (by omega)
  exact Prod.ext hef hbc

theorem actual_outer_eq {n : ℕ} {gs : Groups} (h : ValidPorts n gs)
    (p : Fin (pairCount gs) × Fin 2) :
    (qmaForkOuter (actualSite h) p).val=
      (portAt (groupAt gs (outerPort gs p).1.val) (outerPort gs p).2.val).1 := by
  rcases p with ⟨e,b⟩
  fin_cases b <;> rfl

theorem actual_outer_injective {n : ℕ} {gs : Groups} (h : ValidPorts n gs) :
    Function.Injective (qmaForkOuter (actualSite h)) := by
  intro p q hpq
  have hv := congrArg Fin.val hpq
  rw [actual_outer_eq,actual_outer_eq] at hv
  have he := h.injective (outerPort gs p).1 (outerPort gs q).1
    (outerPort gs p).2 (outerPort gs q).2 hv
  apply outerPort_injective gs
  apply Sigma.ext he.1
  exact (Fin.heq_ext_iff (congrArg (fun i : Fin gs.length => (groupAt gs i.val).length) he.1)).2 he.2

theorem outerPort_index_lt (gs : Groups) (p : Fin (pairCount gs) × Fin 2) :
    (outerPort gs p).2.val < 2*((groupAt gs (outerPort gs p).1.val).length/2) := by
  have hp := (localPair gs p.1).2.isLt
  have hb := p.2.isLt
  dsimp only [outerPort]
  omega

theorem actual_outer_away_retained {n : ℕ} {gs : Groups} (h : ValidPorts n gs)
    (i : Fin gs.length) (j : Fin (groupAt gs i.val).length)
    (hj : 2*((groupAt gs i.val).length/2) ≤ j.val)
    (p : Fin (pairCount gs) × Fin 2) :
    qmaForkOuter (actualSite h) p ≠
      ⟨(portAt (groupAt gs i.val) j.val).1,h.bounded i j⟩ := by
  intro he
  have hv := congrArg Fin.val he
  rw [actual_outer_eq] at hv
  have hh := h.injective (outerPort gs p).1 i (outerPort gs p).2 j hv
  have hl := outerPort_index_lt gs p
  have hlen := congrArg (fun i : Fin gs.length => 2*((groupAt gs i.val).length/2)) hh.1
  rw [hlen] at hl
  omega

theorem actual_outer_away_center {n : ℕ} {gs : Groups} (h : ValidPorts n gs)
    (i : Fin gs.length) (e : Fin (pairCount gs)) :
    actualSite h e 1 ≠ ⟨i.val,lt_of_lt_of_le i.isLt h.centers⟩ ∧
      actualSite h e 2 ≠ ⟨i.val,lt_of_lt_of_le i.isLt h.centers⟩ := by
  constructor
  · intro he
    exact h.disjoint i (localPair gs e).1 (localFirst gs e) (congrArg Fin.val he).symm
  · intro he
    exact h.disjoint i (localPair gs e).1 (localSecond gs e) (congrArg Fin.val he).symm

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListFullDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete literal exchange list has degree at most three once each
active group has at most three ports. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped BigOperators Classical

abbrev PortIndex (gs : Groups) := Σ i : Fin gs.length, Fin (groupAt gs i.val).length

def portSite {n : ℕ} {gs : Groups} (h : ValidPorts n gs) (p : PortIndex gs) : Fin n :=
  ⟨(portAt (groupAt gs p.1.val) p.2.val).1,h.bounded p.1 p.2⟩

theorem portSite_injective {n : ℕ} {gs : Groups} (h : ValidPorts n gs) :
    Function.Injective (portSite h) := by
  intro p q hpq
  have he := h.injective p.1 q.1 p.2 q.2 (congrArg Fin.val hpq)
  apply Sigma.ext he.1
  exact (Fin.heq_ext_iff (congrArg (fun i : Fin gs.length => (groupAt gs i.val).length) he.1)).2 he.2

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

abbrev PointInput := (ℕ × ℕ) × ℚ

def freshPoint (x : PointInput) (j : ℕ) : Port := (x.1.1+2*(x.1.2+j),x.2)

abbrev GroupInput := ℕ × (ℚ × Groups)

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListNext
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

abbrev BondInput := ℕ × (ℕ × (ℚ × Pair))

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpacedListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerate the bounded Manhattan portion of each actual buffered route.
The horizontal and vertical translations are literal binary arithmetic. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpacedListProgram
open ExactQuantumFactoring.BitStackProgram

def budget (A B : ℕ) : ℕ := 8*(9*B+9)*(3*A+2)

end ContinuumCoulomb.QuantumSpacedListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWalkSeek
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded scan finds the first occurrence of a cell in a route list.
It only removes list heads, so the machine state never grows. -/

noncomputable section
open scoped List
namespace ContinuumCoulomb.QuantumWalkSeek
open ExactQuantumFactoring.BitStackProgram
variable {α : Type} [DecidableEq α]

def scan (d : α) (x : α × List α) : α × List α :=
  if x.1 = x.2.headD d then x else (x.1,x.2.tail)

@[simp] theorem scan_first (d : α) (x : α × List α) : (scan d x).1 = x.1 := by
  unfold scan
  split <;> rfl

theorem scan_sublist (d : α) (x : α × List α) : (scan d x).2 <+ x.2 := by
  unfold scan
  split
  · exact List.Sublist.refl _
  · exact List.tail_sublist _

theorem iterate_first (d : α) (x : α × List α) (n : ℕ) : ((scan d)^[n] x).1 = x.1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',scan_first,ih]

theorem iterate_sublist (d : α) (x : α × List α) (n : ℕ) : ((scan d)^[n] x).2 <+ x.2 := by
  induction n with
  | zero => exact List.Sublist.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (scan_sublist d _).trans ih

theorem scan_drop_idx (d a : α) (xs : List α) (n : ℕ) (hn : xs.length ≤ n) :
    ((scan d)^[n] (a,xs)).2 = xs.drop (xs.idxOf a) := by
  induction n generalizing xs with
  | zero =>
    have h : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil =>
      have h : scan d (a,[]) = (a,[]) := by unfold scan; split <;> rfl
      have hi : ((scan d)^[n] (a,[])) = (a,[]) := by
        exact Function.iterate_fixed h n
      rw [h,hi]
      rfl
    | cons b xs =>
      by_cases hab : a=b
      · subst b
        have h : scan d (a,a::xs) = (a,a::xs) := by simp [scan]
        rw [h,Function.iterate_fixed h n]
        simp
      · have hlen : xs.length ≤ n := by simpa using hn
        simpa [scan,hab,List.idxOf_cons,beq_iff_eq,eq_comm] using ih xs hlen

end ContinuumCoulomb.QuantumWalkSeek

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWalkErasureProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial finite-stack implementation of the actual coarse-walk loop
erasure. Each fold output is a sublist of the processed input and initial list. -/

noncomputable section
open scoped List
namespace ContinuumCoulomb.QuantumWalkErasure
open ExactQuantumFactoring.BitStackProgram
variable {α : Type} [DecidableEq α]

theorem fold_sublist (xs bs : List α) :
    xs.foldl (fun ys a => step a ys) bs <+ xs.reverse ++ bs := by
  induction xs generalizing bs with
  | nil => exact List.Sublist.refl _
  | cons a xs ih =>
    simp only [List.foldl_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
    exact (ih (step a bs)).trans ((step_sublist a bs).append_left xs.reverse)

end ContinuumCoulomb.QuantumWalkErasure

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrdinalSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit ordinal ranks give the required injective slots in each bounded
cell fiber. This is the finite ordering used by the spatial output program. -/

namespace ContinuumCoulomb.QuantumOrdinalSlots

def before {n : ℕ} (cells : Fin n → ℕ × ℕ) (q : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun r => r < q ∧ cells r = cells q)

def rank {n : ℕ} (cells : Fin n → ℕ × ℕ) (q : Fin n) : ℕ := (before cells q).card

 theorem rank_lt_fiber {n : ℕ} (cells : Fin n → ℕ × ℕ) (q : Fin n) :
    rank cells q < (Finset.univ.filter (fun r => cells r = cells q)).card := by
  have hs : before cells q ⊆ Finset.univ.filter (fun r => cells r = cells q) := by
    intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hr).2.2⟩
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset hs).mpr
  refine ⟨q,by simp,?_⟩
  simp [before]

 theorem rank_lt {n : ℕ} (cells : Fin n → ℕ × ℕ) {q r : Fin n}
    (hqr : q < r) (hc : cells q = cells r) : rank cells q < rank cells r := by
  have hs : before cells q ⊆ before cells r := by
    intro a ha
    obtain ⟨_,hq,hcell⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq.trans hqr,hcell.trans hc⟩
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset hs).mpr
  refine ⟨q,?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hqr,hc⟩
  · simp [before]

 theorem rank_injective_on_cell {n : ℕ} (cells : Fin n → ℕ × ℕ) {q r : Fin n}
    (hc : cells q = cells r) (hr : rank cells q = rank cells r) : q=r := by
  rcases lt_trichotomy q r with h | h | h
  · have := rank_lt cells h hc
    omega
  · exact h
  · have := rank_lt cells h hc.symm
    omega

end ContinuumCoulomb.QuantumOrdinalSlots

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrdinalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal ordinal-slot program. For an encoded cell list and a unary
label it counts earlier labels in the same cell; the result agrees with the
bounded injective slots used by the spatial construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrdinalProgram
open ExactQuantumFactoring.BitStackProgram

def increment (x : Bool × ℕ) : ℕ := if x.1 then x.2+1 else x.2

theorem fold_increment (xs : List Bool) (k : ℕ) :
    xs.foldl (fun n b => increment (b,n)) k = k+xs.countP id := by
  induction xs generalizing k with
  | nil => simp
  | cons b xs ih =>
    simp only [List.foldl_cons,ih,List.countP_cons]
    cases b <;> simp [increment,Nat.add_comm,Nat.add_left_comm]

end ContinuumCoulomb.QuantumOrdinalProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortRankProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sorted endpoint port is evaluated by counting incident edges whose
lane color is smaller. Each record contains the two endpoints and lane color. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortRankProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Entry := ℕ × (ℕ × ℕ)

end ContinuumCoulomb.QuantumPortRankProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform incidence bounds for the actual ordered local reductions.  Every
new site belongs to one input term, while old sites remain in that term's
stored support.  The bound counts zero-coefficient terms as well. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedIncidence
open scoped BigOperators Classical

variable {ι κ : Type} [Fintype κ]

def count (xs : κ → List ι) (q : ι) : ℕ :=
  ∑ e, if q ∈ xs e then 1 else 0

def Bounded (xs : κ → List ι) (D : ℕ) : Prop := ∀ q, count xs q ≤ D

def Origin (xs : κ → List ι) (e : κ) : ι ⊕ κ → Prop :=
  Sum.elim (fun q => q ∈ xs e) (fun f => f = e)

omit [Fintype κ] in
theorem append_origin (xs : κ → List ι) (e : κ) (zs : List ι)
    (hz : ∀ q ∈ zs, q ∈ xs e) (q : ι ⊕ κ)
    (hq : q ∈ QuantumOrderedSubdivision.appendMediator zs e) : Origin xs e q := by
  cases q with
  | inl q =>
    exact hz q (by simpa only [QuantumOrderedSubdivision.appendMediator,
      List.mem_append,List.mem_map,Sum.inl.injEq,exists_eq_right,List.mem_singleton,
      Sum.inl_ne_inr,or_false] using hq)
  | inr q =>
    simpa only [Origin,Sum.elim_inr,QuantumOrderedSubdivision.appendMediator,
      List.mem_append,List.mem_map,Sum.inl_ne_inr,and_false,exists_false,List.mem_singleton,
      Sum.inr.injEq,false_or] using hq

omit [Fintype κ] in
theorem subdivision_origin (xs : κ → List ι) (d : ℕ)
    (p : κ × Fin 4) (q : ι ⊕ κ)
    (hq : q ∈ QuantumOrderedSubdivision.outputSites xs d p) : Origin xs p.1 q := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · simp [QuantumOrderedSubdivision.outputSites] at hq
  · have he : q=Sum.inr e := by simpa [QuantumOrderedSubdivision.outputSites] using hq
    subst q
    rfl
  · exact append_origin xs e _ (fun _ h => List.mem_of_mem_take h) q hq
  · exact append_origin xs e _ (fun _ h => List.mem_of_mem_drop h) q hq

omit [Fintype κ] in
theorem yy_origin (xs : κ → List ι) (p : κ × Fin 4) (q : ι ⊕ κ)
    (hq : q ∈ QuantumOrderedYY.outputSites xs p) : Origin xs p.1 q := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · simp [QuantumOrderedYY.outputSites] at hq
  · have he : q=Sum.inr e := by simpa [QuantumOrderedYY.outputSites] using hq
    subst q
    rfl
  · exact append_origin xs e _ (fun _ h => h) q hq
  · exact append_origin xs e _ (fun _ h => h) q hq

omit [Fintype κ] in
theorem third_origin (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 3) (p : κ × Fin 7) (q : ι ⊕ κ)
    (hq : q ∈ QuantumOrderedThird.outputSites xs w p) : Origin xs p.1 q := by
  rcases p with ⟨e,k⟩
  have hp : ∀ i ∈ (QuantumOrderedTriple.partition (xs e) (w e)).1, i ∈ xs e := by
    intro i hi
    exact (QuantumOrderedTriple.partition_spec (xs e) (w e) (hlen e)).1.mem_iff.mp
      (List.mem_append_left _ hi)
  have hr : ∀ i ∈ (QuantumOrderedTriple.partition (xs e) (w e)).2, i ∈ xs e := by
    intro i hi
    exact (QuantumOrderedTriple.partition_spec (xs e) (w e) (hlen e)).1.mem_iff.mp
      (List.mem_append_right _ hi)
  fin_cases k
  · simp [QuantumOrderedThird.outputSites] at hq
  · have he : q=Sum.inr e := by simpa [QuantumOrderedThird.outputSites] using hq
    subst q
    rfl
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    exact hp i hi
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    exact hr i hi
  · exact append_origin xs e _ hr q hq
  · exact append_origin xs e _ (fun i h => hp i (List.mem_of_mem_take h)) q hq
  · exact append_origin xs e _ (fun i h => hp i (List.mem_of_mem_drop h)) q hq

end ContinuumCoulomb.QuantumOrderedIncidence

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSpatialComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial data for the literal ordered six-stage compiler. A mediator is
placed in its parent term's cell, and each emitted term retains that anchor. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSpatialComplete
open scoped Classical
variable {ι κ C : Type}

def extendCell (cell : ι → C) (anchor : κ → C) : ι ⊕ κ → C := Sum.elim cell anchor
def extendAnchor (d : ℕ) (anchor : κ → C) : κ × Fin d → C := fun p => anchor p.1

theorem extension_geometry {d : ℕ} (xs : κ → List ι)
    (ys : κ × Fin d → List (ι ⊕ κ)) (cell : ι → C) (anchor : κ → C)
    (R : C → C → Prop) (hR : ∀ p, R p p)
    (hx : ∀ e q, q ∈ xs e → R (cell q) (anchor e))
    (hy : ∀ e q, q ∈ ys e → QuantumOrderedIncidence.Origin xs e.1 q) :
    ∀ e q, q ∈ ys e → R (extendCell cell anchor q) (extendAnchor d anchor e) := by
  intro e q hq
  have ho := hy e q hq
  cases q with
  | inl q => exact hx e.1 q ho
  | inr q =>
    change q=e.1 at ho
    subst q
    exact hR _

theorem extendCell_density [Fintype ι] [Fintype κ] (cell : ι → C) (anchor : κ → C)
    {A B : ℕ} (hc : ∀ p, (Finset.univ.filter (fun q => cell q=p)).card ≤ A)
    (ha : ∀ p, (Finset.univ.filter (fun e => anchor e=p)).card ≤ B) (p : C) :
    (Finset.univ.filter (fun q => extendCell cell anchor q=p)).card ≤ A+B := by
  rw [qmaSumFilter_card]
  exact Nat.add_le_add (hc p) (ha p)

theorem extendAnchor_density [Fintype κ] (d : ℕ) (anchor : κ → C) {B : ℕ}
    (ha : ∀ p, (Finset.univ.filter (fun e => anchor e=p)).card ≤ B) (p : C) :
    (Finset.univ.filter (fun e => extendAnchor d anchor e=p)).card ≤ d*B := by
  change (Finset.univ.filter (fun e : κ × Fin d => anchor e.1=p)).card ≤ _
  rw [qmaProdFilter_card d (fun e : κ => anchor e=p)]
  exact Nat.mul_le_mul_left d (ha p)

def cell1 (cell : ι → C) (anchor : κ → C) := extendCell cell anchor
def anchor1 (anchor : κ → C) := extendAnchor 4 anchor
def cell2 (cell : ι → C) (anchor : κ → C) := extendCell (cell1 cell anchor) (anchor1 anchor)
def anchor2 (anchor : κ → C) := extendAnchor 4 (anchor1 anchor)
def cell3 (cell : ι → C) (anchor : κ → C) := extendCell (cell2 cell anchor) (anchor2 anchor)
def anchor3 (anchor : κ → C) := extendAnchor 7 (anchor2 anchor)
def cell4 (cell : ι → C) (anchor : κ → C) := extendCell (cell3 cell anchor) (anchor3 anchor)
def anchor4 (anchor : κ → C) := extendAnchor 4 (anchor3 anchor)
def cell5 (cell : ι → C) (anchor : κ → C) := extendCell (cell4 cell anchor) (anchor4 anchor)
def anchor5 (anchor : κ → C) := extendAnchor 7 (anchor4 anchor)
def cell6 (cell : ι → C) (anchor : κ → C) := extendCell (cell5 cell anchor) (anchor5 anchor)
def anchor6 (anchor : κ → C) := extendAnchor 4 (anchor5 anchor)

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem complete_geometry (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (cell : ι → C) (anchor : κ → C)
    (R : C → C → Prop) (hR : ∀ p, R p p)
    (hx : ∀ e q, q ∈ xs e → R (cell q) (anchor e)) :
    ∀ e q, q ∈ QuantumOrderedPrivate.outputSites (QuantumOrderedXZ.sites xs w) e →
      R (cell6 cell anchor q) (anchor6 anchor e) := by
  have h1 := extension_geometry xs _ cell anchor R hR hx
    (QuantumOrderedIncidence.subdivision_origin xs 3)
  have h2 := extension_geometry (QuantumOrderedSubdivision.outputSites xs 3) _
    (cell1 cell anchor) (anchor1 anchor) R hR h1
    (QuantumOrderedIncidence.subdivision_origin (QuantumOrderedSubdivision.outputSites xs 3) 2)
  have h3 := extension_geometry (QuantumOrderedXZ.threeSites xs) (QuantumOrderedXZ.twoSites xs w)
    (cell2 cell anchor) (anchor2 anchor) R hR h2
    (QuantumOrderedIncidence.third_origin (QuantumOrderedXZ.threeSites xs)
      (QuantumOrderedXZ.threeWord xs w) (QuantumOrderedXZ.threeSites_length xs hlen))
  have h4 := extension_geometry (QuantumOrderedXZ.twoSites xs w) _
    (cell3 cell anchor) (anchor3 anchor) R hR h3
    (QuantumOrderedIncidence.yy_origin _)
  have h5 := extension_geometry (QuantumOrderedXZ.xzThreeSites xs w) (QuantumOrderedXZ.sites xs w)
    (cell4 cell anchor) (anchor4 anchor) R hR h4
    (QuantumOrderedIncidence.third_origin (QuantumOrderedXZ.xzThreeSites xs w)
      (QuantumOrderedXZ.xzThreeWord xs w) (QuantumOrderedXZ.xzThreeSites_length xs w hlen))
  exact extension_geometry (QuantumOrderedXZ.sites xs w) _
    (cell5 cell anchor) (anchor5 anchor) R hR h5
    (QuantumOrderedIncidence.subdivision_origin _ 1)

omit [DecidableEq ι] [DecidableEq κ] in
theorem complete_density (cell : ι → C) (anchor : κ → C) {A B : ℕ}
    (hc : ∀ p, (Finset.univ.filter (fun q => cell q=p)).card ≤ A)
    (ha : ∀ p, (Finset.univ.filter (fun e => anchor e=p)).card ≤ B) :
    (∀ p, (Finset.univ.filter (fun q => cell6 cell anchor q=p)).card ≤ A+3717*B) ∧
    (∀ p, (Finset.univ.filter (fun e => anchor6 anchor e=p)).card ≤ 12544*B) := by
  have hc1 := extendCell_density cell anchor hc ha
  have ha1 := extendAnchor_density 4 anchor ha
  have hc2 := extendCell_density (cell1 cell anchor) (anchor1 anchor) hc1 ha1
  have ha2 := extendAnchor_density 4 (anchor1 anchor) ha1
  have hc3 := extendCell_density (cell2 cell anchor) (anchor2 anchor) hc2 ha2
  have ha3 := extendAnchor_density 7 (anchor2 anchor) ha2
  have hc4 := extendCell_density (cell3 cell anchor) (anchor3 anchor) hc3 ha3
  have ha4 := extendAnchor_density 4 (anchor3 anchor) ha3
  have hc5 := extendCell_density (cell4 cell anchor) (anchor4 anchor) hc4 ha4
  have ha5 := extendAnchor_density 7 (anchor4 anchor) ha4
  have hc6 := extendCell_density (cell5 cell anchor) (anchor5 anchor) hc5 ha5
  have ha6 := extendAnchor_density 4 (anchor5 anchor) ha5
  constructor
  · intro p
    exact (hc6 p).trans (by omega)
  · intro p
    exact (ha6 p).trans (by omega)

end ContinuumCoulomb.QuantumOrderedSpatialComplete

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical merging of a finite bond tape. A quadratic table of vertex pairs
gives a deterministic order and retains exactly the pairs occurring in the input. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListMerge

abbrev Pair := ℕ × ℕ

def pairs (n : ℕ) : List Pair := (List.range n).product (List.range n)

theorem pairs_nodup (n : ℕ) : (pairs n).Nodup :=
  List.nodup_range.product List.nodup_range

end ContinuumCoulomb.QuantumListMerge

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFiniteRouteSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The 140-candidate route search uses a literal fixed-size scan. Its input
predicate can be supplied by the finite physical geometry table. -/

namespace ContinuumCoulomb.QuantumFiniteRouteSearch
open ExactQuantumFactoring.BitStackProgram

def firstTrue : ℕ → List Bool → ℕ
  | 0, _ => 0
  | k+1, bs => if bs.headD false then 0 else 1+firstTrue k bs.tail

end ContinuumCoulomb.QuantumFiniteRouteSearch

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumParallelRouteSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The predicate mask and the path list have the same 140-entry order.
Searching the mask therefore returns the path of the actual first permitted
catalog route, without encoding proof-carrying route objects. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFiniteRouteSearch
open ExactQuantumFactoring.BitStackProgram

def selectParallelValue {β : Type} (default : β) (x : List β × List Bool) : β :=
  (x.1.drop (firstTrue 140 x.2)).headD default

end ContinuumCoulomb.QuantumFiniteRouteSearch

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

def step (x : Bool × ℕ) : ℕ := if x.1 then 0 else x.2+1

theorem step_le (b : Bool) (n : ℕ) : step (b,n) ≤ n+1 := by
  cases b <;> simp [step]

theorem fold_le (xs : List Bool) (n : ℕ) :
    xs.foldl (fun k b => step (b,k)) n ≤ xs.length+n := by
  induction xs generalizing n with
  | nil => simp
  | cons b xs ih =>
    have h := ih (step (b,n))
    have hs := step_le b n
    simp only [List.foldl_cons,List.length_cons]
    omega

def first (xs : List Bool) : ℕ := xs.foldr (fun b n => step (b,n)) 0

theorem first_eq_findIdx (xs : List Bool) : first xs=xs.findIdx id := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b <;> simp [first,step,List.findIdx_cons,← ih,Nat.add_comm]

end ContinuumCoulomb.QuantumFirstUseProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fork round keeps each new pair in the coarse cell of its active center. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
variable {n c : ℕ} {d : Fin c → ℕ} {β : Type*}

def qmaCellMass {V : Type*} [Fintype V] [DecidableEq β] (cell : V → β) (x : β) : ℕ :=
  ∑ v, if cell v = x then 1 else 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkInitialCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial private ports and all subsequent fork vertices retain bounded cell density. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
variable {n m : ℕ} {β : Type*}

theorem qmaOriginalPortEquiv_endpoint (left right : Fin m → Fin n)
    (p : Σ i, Fin (qmaOriginalPortCount left right i)) :
    qmaOriginalEndpoint left right (qmaOriginalPortEquiv left right p) = p.1 :=
  ((Fintype.equivFin {q : Fin m × Fin 2 // qmaOriginalEndpoint left right q = p.1}).symm p.2).property

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListCellMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal fork round has bounded density in the original coarse cells.
The proof counts its actual fresh indices through the ordered pair catalog. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped BigOperators Classical
variable {β : Type*} [DecidableEq β]

theorem prefix_cell_mass_le (m n : ℕ) (h : m ≤ n) (cell : ℕ → β) (p : β) :
    qmaCellMass (fun i : Fin m => cell i.val) p ≤
      qmaCellMass (fun i : Fin n => cell i.val) p := by
  unfold qmaCellMass
  change (∑ i : Fin m, if cell i.val=p then 1 else 0) ≤
    ∑ i : Fin n, if cell i.val=p then 1 else 0
  calc
    _ = ∑ i ∈ Finset.range m, if cell i=p then 1 else 0 :=
      Fin.sum_univ_eq_sum_range (fun i => if cell i=p then 1 else 0) m
    _ ≤ ∑ i ∈ Finset.range n, if cell i=p then 1 else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun i _ _ => Nat.zero_le _)
    _ = _ := (Fin.sum_univ_eq_sum_range (fun i => if cell i=p then 1 else 0) n).symm

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The route-array filter selects exactly the same source indices as the
literal work-list filter, preserving their order. -/

namespace ContinuumCoulomb.QuantumListRouteProgram

theorem headD_drop {α : Type} (xs : List α) (d : α) (i : Fin xs.length) :
    (xs.drop i.val).headD d=xs.get i := by
  rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem i.isLt]
  rfl

end ContinuumCoulomb.QuantumListRouteProgram

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
open scoped Classical

def role {a b : ℕ} (e : Fin a ≃ Fin b) (p : Fin a × Fin 3) :
    Fin b ⊕ (Fin b × Fin 2) :=
  ![.inl (e p.1),.inr (e p.1,0),.inr (e p.1,1)] p.2

def unrole {a b : ℕ} (e : Fin a ≃ Fin b) :
    Fin b ⊕ (Fin b × Fin 2) → Fin a × Fin 3
  | .inl i => (e.symm i,0)
  | .inr (i,k) => (e.symm i,k.succ)

def roleEquiv {a b : ℕ} (e : Fin a ≃ Fin b) :
    (Fin a × Fin 3) ≃ (Fin b ⊕ (Fin b × Fin 2)) where
  toFun := role e
  invFun := unrole e
  left_inv := by
    rintro ⟨i,k⟩
    fin_cases k <;> simp [role,unrole]
  right_inv := by
    rintro (i | ⟨i,k⟩)
    · simp [role,unrole]
    · fin_cases k <;> simp [role,unrole]

end ContinuumCoulomb.QuantumListSchedule

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
open scoped Classical

def spatialDensity (A D : ℕ) : ℕ := ((1+2*D)^D*(D+1))*A

end ContinuumCoulomb.QuantumForkList

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
open ExactQuantumFactoring.BitStackProgram QuantumForkList

opaque roundValue (A D : ℕ) : { k : ℕ //
    QMASpatialExchangeModel.routeLengthBound (spatialDensity A D) (27*spatialDensity A D)=k } :=
  ⟨QMASpatialExchangeModel.routeLengthBound (spatialDensity A D) (27*spatialDensity A D),rfl⟩
def rounds (A D : ℕ) : ℕ := (roundValue A D).val
theorem rounds_eq (A D : ℕ) :
    QMASpatialExchangeModel.routeLengthBound (spatialDensity A D) (27*spatialDensity A D)=
      rounds A D := (roundValue A D).property

end ContinuumCoulomb.QuantumSpatialPortProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLatticeSerialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal serialization of rational lattice graphs into the published source
format. The constant matrix offset is subtracted from both thresholds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumLatticeSerialization
open ExactQuantumFactoring.BitStackProgram

abbrev Coordinate := ℤ × ℤ

end ContinuumCoulomb.QuantumLatticeSerialization

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLatticeEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite source objects serialize to valid binary instances with canonical
rational coefficients and the same physical sites and thresholds. -/

namespace ContinuumCoulomb.SquareLatticeHeisenberg

theorem get_ofFn_value {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (hi : i < n) :
    (List.ofFn f).get ⟨i,by simpa using hi⟩ = f ⟨i,hi⟩ := by
  simp [List.get_eq_getElem]

end ContinuumCoulomb.SquareLatticeHeisenberg

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
open ExactQuantumFactoring.BitStackProgram

opaque roundsValue : {k : ℕ // k=80} := ⟨80,rfl⟩
def rounds : ℕ := roundsValue.val

end ContinuumCoulomb.QuantumFinalRoutingProgram

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

-- Match the domain decision used inside the generic coefficient definition;
-- otherwise two propositionally equal Pi enumerations force proof reduction.
local instance finDecision (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def matrixData {β : Type} [Fintype β] (A : Matrix β β Scalar) : List Scalar :=
  (enumerate (β×β)).map (fun p => A p.1 p.2)

def entry {β : Type} [Fintype β] (xs : List Scalar) (s t : β) : Scalar :=
  (xs.drop ((Fintype.equivFin (β×β)) (s,t)).val).headD (rat 0)

theorem entry_matrixData {β : Type} [Fintype β]
    (A : Matrix β β Scalar) (s t : β) : entry (matrixData A) s t = A s t := by
  simp only [entry,matrixData,enumerate,List.map_ofFn,List.headD_eq_head?_getD,
    List.head?_drop,List.getElem?_ofFn,Fin.isLt,↓reduceDIte,Option.getD_some,
    Function.comp_apply,Fin.eta,Equiv.symm_apply_apply]

end ContinuumCoulomb.QuantumFixedPauli

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational-register tables for every actual ordered history term.
Only the propagation core is multiplied, so its summation has at most
32 states regardless of the number of spectator qubits. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

def diagonal {α : Type} [DecidableEq α] (f : α → ℚ) : Matrix α α Scalar :=
  fun s t => if s = t then rat (f s) else rat 0

end ContinuumCoulomb.QuantumAlgebraicHistory

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

def gramData {β : Type} [Fintype β] (xs : List Scalar) : List Scalar :=
  matrixData (matMul (adjoint (fun s t : β => entry xs s t)) (fun s t : β => entry xs s t))

theorem gramData_matrixData {β : Type} [Fintype β] (A : Matrix β β Scalar) :
    gramData (β := β) (matrixData A) = matrixData (matMul (adjoint A) A) := by
  have h : (fun s t : β => entry (matrixData A) s t) = A := by
    funext s t
    exact entry_matrixData A s t
  simp only [gramData,h]

end ContinuumCoulomb.QuantumFixedMatrix

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial coefficient envelopes for the parallel fork used by the literal
compiler. Both retained bonds and active pairs fit the same size bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped BigOperators Classical

def forkBudget (M L : ℝ) : ℝ :=
  3*M*L+L+3*M*(1+4*L)+12*M*(1+2*L)^2+1

def forkRadius (M L T : ℝ) : ℝ :=
  L+16*(forkBudget M L)^3*T+4*forkBudget M L+1

def forkCoefficient (M L T : ℝ) : ℝ :=
  1+L+(10*M+2)*(forkRadius M L T)^2

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial size bounds for the actual finite lists. A fixed number of
rounds grows the spin and bond counts linearly in the initial active-port mass. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped BigOperators Classical

def portMass (gs : Groups) : ℕ := (gs.map List.length).sum

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListIterateWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iterating a fixed number of literal fork rounds preserves a polynomial
coefficient bound. Size uses one uniform envelope for all intermediate lists. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList

def coefficientEnvelope (M L T : ℝ) : ℕ → ℝ
  | 0 => L
  | k+1 => forkCoefficient M (coefficientEnvelope M L T k) T

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListOutputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single explicit coefficient envelope for every edge in the actual
output, including the retained active-star edges, and for its scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList

def outputCoefficient (m D : ℕ) (L T : ℝ) : ℝ :=
  let M : ℝ := ((8*D+3)*m:ℕ)
  coefficientEnvelope M (forkCoefficient M L T) T D

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListBoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal unary programs compute the coefficient envelopes. For each fixed
number of rounds, the complete numerical envelope is polynomial in its inputs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

def budgetNat (M L : ℕ) : ℕ := 3*M*L+L+3*M*(1+4*L)+12*M*(1+2*L)^2+1
def radiusNat (M L T : ℕ) : ℕ := L+16*(budgetNat M L)^3*T+4*budgetNat M L+1
def coefficientNat (M L T : ℕ) : ℕ := 1+L+(10*M+2)*(radiusNat M L T)^2
def envelopeNat (M L T : ℕ) : ℕ → ℕ
  | 0 => L
  | k+1 => coefficientNat M (envelopeNat M L T k) T

@[simp] theorem budgetNat_cast (M L : ℕ) : (budgetNat M L:ℝ)=forkBudget M L := by
  simp [budgetNat,forkBudget]
@[simp] theorem radiusNat_cast (M L T : ℕ) : (radiusNat M L T:ℝ)=forkRadius M L T := by
  simp [radiusNat,forkRadius]
@[simp] theorem coefficientNat_cast (M L T : ℕ) :
    (coefficientNat M L T:ℝ)=forkCoefficient M L T := by
  simp [coefficientNat,forkCoefficient]
@[simp] theorem envelopeNat_cast (M L T k : ℕ) :
    (envelopeNat M L T k:ℝ)=coefficientEnvelope M L T k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [envelopeNat,coefficientNat_cast,ih,coefficientEnvelope]

def outputCoefficientNat (m D L T : ℕ) : ℕ :=
  let M := (8*D+3)*m
  envelopeNat M (coefficientNat M L T) T D

@[simp] theorem outputCoefficientNat_cast (m D L T : ℕ) :
    (outputCoefficientNat m D L T:ℝ)=outputCoefficient m D L T := by
  simp only [outputCoefficientNat,envelopeNat_cast,coefficientNat_cast,outputCoefficient]

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateScalarReduction
attribute [-simp] _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.realHeight_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.realHeight_rat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar reduction of a one-site gate tensor to its active entry
and spectator equality test. This avoids an ambient spin-basis sum in the
literal history-matrix evaluator. -/

noncomputable section
namespace ContinuumCoulomb.QuantumGateScalarReduction
open QuantumAlgebraicScalar QuantumFixedPauli QuantumAlgebraicHistory
open scoped Classical

@[simp] theorem mul_one (x : Scalar) : mul x (rat 1)=x := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp [mul,rat,realRat,realMul,realSub,realAdd,realNeg]

@[simp] theorem one_mul (x : Scalar) : mul (rat 1) x=x := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp [mul,rat,realRat,realMul,realSub,realAdd,realNeg]

@[simp] theorem mul_zero (x : Scalar) : mul x (rat 0)=rat 0 := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp [mul,rat,realRat,realMul,realSub,realAdd,realNeg]

@[simp] theorem zero_mul (x : Scalar) : mul (rat 0) x=rat 0 := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp [mul,rat,realRat,realMul,realSub,realAdd,realNeg]

def sparseEntry {α : Type} [DecidableEq α] (i : α)
    (A : Fin 2 → Fin 2 → Scalar) (s t : α → Fin 2) : Scalar :=
  if ∀ j, j ≠ i → s j=t j then A (s i) (t i) else rat 0

end ContinuumCoulomb.QuantumGateScalarReduction

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedPauli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-width Pauli tables.  Padding a local word duplicates its coefficient
by a known factor; replacing odd-Y zero terms by the identity keeps every
emitted word real without a dependent filtered index type. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedPauli
open scoped BigOperators Classical

def splitWords (n m : ℕ) : (Fin (n+m) → Fin 4) ≃
    ((Fin n → Fin 4) × (Fin m → Fin 4)) :=
  ((finSumFinEquiv.symm).arrowCongr (Equiv.refl (Fin 4))).trans
    (Equiv.sumArrowEquivProdArrow (Fin n) (Fin m) (Fin 4))

def restrictWord (n m : ℕ) (w : Fin (n+m) → Fin 4) : Fin n → Fin 4 :=
  fun i => w (Fin.castAdd m i)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def evenWord (w : ι → Fin 4) : ι → Fin 4 :=
  if Even (qmaPauliYCount w) then w else fun _ => 0

def evenCoefficient (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (w : ι → Fin 4) : ℝ :=
  if Even (qmaPauliYCount w) then (qmaPauliCoefficient A w).re else 0

def paddedWord (n m : ℕ) (w : Fin (n+m) → Fin 4) : Fin n → Fin 4 :=
  evenWord (restrictWord n m w)

def paddedCoefficient (n m : ℕ)
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (w : Fin (n+m) → Fin 4) : ℝ :=
  evenCoefficient A (restrictWord n m w)/(4:ℝ)^m

end ContinuumCoulomb.QuantumPaddedPauli

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

def word {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S}) (m : ℕ)
    (w : Fin (n+m) → Fin 4) : ι → Fin 4 :=
  qmaPauliExtend S (fun i => QuantumPaddedPauli.paddedWord n m w (e.symm i))

end ContinuumCoulomb.QuantumPaddedLocal

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

def widthIndex (n : ℕ) (hn : n ≤ 6) :
    (Fin 6 → Fin 4) ≃ (Fin (n+(6-n)) → Fin 4) :=
  Equiv.cast (by rw [Nat.add_sub_of_le hn])

end ContinuumCoulomb.QuantumPaddedHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSourceIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit finite sum/product indices for the history qubits and padded
terms. Their natural values are the literal support-list site numbers. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSourceIndex
open scoped Classical

abbrev Pattern := Fin 6 → Fin 4
def patternCount : ℕ := Fintype.card Pattern

end ContinuumCoulomb.QuantumOrderedSourceIndex

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual padded history word is obtained by zipping its literal
site-number list with a fixed local pattern. No spectator basis occurs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedHistory
open scoped Classical

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def localLabels (n m : ℕ) (w : Fin (n+m) → Fin 4) : List ℕ :=
  List.ofFn (fun i => (QuantumPaddedPauli.paddedWord n m w i).val)

end ContinuumCoulomb.QuantumPaddedHistory

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

local instance finDecision (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def coefficient (n m : ℕ) (xs : List Scalar) (w : Fin (n+m) → Fin 4) : RealScalar :=
  let v := QuantumPaddedPauli.restrictWord n m w
  if Even (qmaPauliYCount v) then
    realMul (realRat (((4:ℚ)^m)⁻¹))
      (realCoefficient (fun s t : Fin n → Fin 2 => entry xs s t) v)
  else realRat 0

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

local instance finDecision (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end ScalarTable

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

abbrev Input := ℕ × (List ℕ × List Scalar)

def labels (n m : ℕ) (w : Fin (n+m) → Fin 4) (xs : List ℕ) : List Letter :=
  List.ofFn (fun i : Fin n => ((xs.drop i.val).headD 0,
    (QuantumPaddedPauli.paddedWord n m w i).val))

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelMeaning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every emitted local packet entry is the actual padded history word
and its sampled coefficient, in the supplied support-list order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open scoped Classical

-- The padded scalar table uses this same finite-domain decision.  Matching it
-- keeps the fixed matrix enumeration opaque during the source-entry proof.
local instance finDecision (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

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

theorem pattern_card (n : ℕ) (hn : n ≤ 6) :
    Fintype.card (Fin (n+(6-n)) → Fin 4) = QuantumOrderedSourceIndex.patternCount := by
  simp only [QuantumOrderedSourceIndex.patternCount,QuantumOrderedSourceIndex.Pattern,
    Fintype.card_fun,Fintype.card_fin,Nat.add_sub_of_le hn]

def packetPatterns (n : ℕ) (hn : n ≤ 6) :
    Fin QuantumOrderedSourceIndex.patternCount ≃ (Fin (n+(6-n)) → Fin 4) :=
  (finCongr (pattern_card n hn).symm).trans (Fintype.equivFin _).symm

local instance tableFinDecision (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryIncidence
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

theorem padded_bound {ι κ ν : Type} [Fintype κ] [Fintype ν]
    (xs : κ → List ι) {D : ℕ} (hx : Bounded xs D) :
    Bounded (fun p : κ × ν => xs p.1) (Fintype.card ν*D) := by
  intro q
  calc
    count (fun p : κ × ν => xs p.1) q = Fintype.card ν*count xs q := by
      rw [count,Fintype.sum_prod_type]
      have hi (e : κ) : (∑ _k : ν, if q ∈ xs e then 1 else 0) =
          Fintype.card ν*(if q ∈ xs e then 1 else 0) := by
        by_cases h : q ∈ xs e <;> simp [h]
      simp_rw [hi]
      exact (Finset.mul_sum _ _ _).symm
    _ ≤ Fintype.card ν*D := Nat.mul_le_mul_left _ (hx q)

end ContinuumCoulomb.QuantumHistoryIncidence

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal four-spin exchange list preserves a uniform incidence bound.
All bonds are counted, including bonds with zero weight. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawIncidence
open QuantumForkList QuantumOrderedIncidence QuantumRawExchange
open scoped BigOperators Classical

def sites {n : ℕ} : QMAXZTerm n → List (Fin n)
  | .scalar => []
  | .field i _ => [i]
  | .pair i j _ _ _ => [i,j]

theorem slot_div (i : ℕ) (j : Fin 4) : (4*i+j.val)/4=i := by omega

theorem ofSites_subset {n : ℕ} (xs : List (Fin n)) (w : Fin n → Fin 4) :
    ∀ i ∈ sites (QuantumOrderedXZTerm.ofSites xs w), i ∈ xs := by
  cases xs with
  | nil => simp [QuantumOrderedXZTerm.ofSites,sites]
  | cons i xs =>
    cases xs with
    | nil =>
      by_cases h : w i=0 <;>
        simp [QuantumOrderedXZTerm.ofSites,QuantumOrderedXZTerm.field,sites,h]
    | cons j xs =>
      by_cases hij : i=j <;> by_cases hi : w i=0 <;> by_cases hj : w j=0 <;>
        simp [QuantumOrderedXZTerm.ofSites,QuantumOrderedXZTerm.field,sites,hij,hi,hj]

theorem numbered_bound {ι κ : Type} [Fintype κ] {n m D : ℕ}
    (q : Fin n ≃ ι) (e : Fin m ≃ κ) (xs : κ → List ι) (hx : Bounded xs D) :
    Bounded (QuantumOrderedLabelTable.numberedSites q e xs) D := by
  intro i
  have hm (a : Fin m) :
      i ∈ QuantumOrderedLabelTable.numberedSites q e xs a ↔ q i ∈ xs (e a) := by
    simp only [QuantumOrderedLabelTable.numberedSites,List.mem_map]
    constructor
    · rintro ⟨j,hj,hji⟩
      have hj' : j=q i := by simpa using congrArg q hji
      simpa only [hj'] using hj
    · intro hi
      exact ⟨q i,hi,q.symm_apply_apply i⟩
  calc
    count (QuantumOrderedLabelTable.numberedSites q e xs) i =
        ∑ a : Fin m, if q i ∈ xs (e a) then 1 else 0 := by simp only [count,hm]
    _ = count xs (q i) := by
      rw [count]
      exact e.sum_comp (fun a => if q i ∈ xs a then (1:ℕ) else 0)
    _ ≤ D := hx (q i)

end ContinuumCoulomb.QuantumRawIncidence

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed degree bound for the literal raw history output. Consequently a
constant number of literal fork rounds suffices. -/

noncomputable section
namespace ContinuumCoulomb
open QuantumOrderedIncidence QuantumRawIncidence QuantumOrderedLabelTable
open scoped Classical

namespace QuantumPaddedLabelProgram
open QuantumPaddedHistory QuantumOrderedSourceIndex QuantumForkList

def historyDegree : ℕ := 6+22*29595009024

end QuantumPaddedLabelProgram
end ContinuumCoulomb

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

def rawDensity : ℕ := 4*(45+3717*(4096*64))
def finalDensity : ℕ := spatialDensity rawDensity historyDegree

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

theorem spatialDensity_pos (A D : ℕ) (hA : 0 < A) : 0 < spatialDensity A D := by
  unfold spatialDensity
  exact Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) D) (Nat.succ_pos D)) hA

theorem finalDensity_pos : 0 < finalDensity := spatialDensity_pos rawDensity historyDegree (by decide)

-- The certified value is fixed, but need never be expanded into a numeral.
opaque routeRoundValue : { k : ℕ //
    QMASpatialExchangeModel.routeLengthBound (spatialDensity rawDensity historyDegree)
      (27*spatialDensity rawDensity historyDegree) = k } :=
  ⟨QMASpatialExchangeModel.routeLengthBound (spatialDensity rawDensity historyDegree)
    (27*spatialDensity rawDensity historyDegree),rfl⟩

def routeRounds : ℕ := routeRoundValue.val
def totalRounds : ℕ := historyDegree+routeRounds+83

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedOutputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial envelopes apply to the actual emitted rational graph,
with the same six-stage table and four-spin instructions used by its energy proof. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelCompile
open QuantumOrderedLabelTable
open scoped Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {n m : ℕ}

def coefficientEnvelope (n m B N : ℕ) : ℕ := QuantumRawExchange.outputNat
  (n+3717*m) (12544*m) (QuantumOrderedXZ.pipelineNat m B N 6) N

end ContinuumCoulomb.QuantumOrderedLabelCompile

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryParameterBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial powers for the actual history coefficients. These
bounds are in the retained history-qubit count, not in an auxiliary circuit. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumOrderedSourceIndex QuantumAlgebraicHistory
open QuantumCoefficientPrograms

def parameterEnvelope (rounds n : ℕ) : ℕ :=
  n+8192*n+128*(14+288*((14*(n+1)+8)*n))+60*(rounds+9)*(n+1)+1

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySizeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear size and box bounds for the exact spatial graph before routing. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumOrderedSourceIndex QuantumPaddedLabelProgram QuantumForkList

def rawBondFactor : ℕ := 6*(1+3717*8192)+22*(12544*8192)
def spatialSizeFactor (D : ℕ) : ℕ := 4*(1+3717*8192)+(5+12*D)*rawBondFactor

def boxFactor (A B : ℕ) : ℕ := 256*(8*(9*B+9))*(A+1)

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGeometryPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One uniform power bounds all finite geometric inputs of the actual
history-to-lattice coefficient program. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumOrderedSourceIndex QuantumForkList QuantumPaddedLabelProgram

attribute [local irreducible] spatialDensity

def geometryEnvelope (A B D R n : ℕ) : ℕ :=
  rawBondFactor*n+spatialSizeFactor D*n+spatialSizeFactor D*n*R+
    boxFactor A B*(n+1)+1

end ContinuumCoulomb.QuantumHistorySpatial

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

abbrev Input := ℕ × (List ℕ × List ℕ)

def value (x : Input) : ℕ := (x.2.2.drop (x.2.1.idxOf x.1)).headD 0

open scoped Classical

def readBit (x : Input) : Fin 2 := ⟨value x % 2,Nat.mod_lt _ (by decide)⟩

end ContinuumCoulomb.QuantumSupportLookup

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryBitProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal bit reads for the small history tables, and a bounded Boolean
scan.  The register bound is unary; this scan has no spin-configuration loop. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryBitProgram
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar

abbrev Data := List ℕ × (List ℕ × List ℕ)
abbrev Query := ℕ × Data

def bit (n : ℕ) : Fin 2 := ⟨n % 2,Nat.mod_lt _ (by decide)⟩

def row (d : Data) (q : ℕ) : Fin 2 :=
  bit (QuantumSupportLookup.value (q,d.1,d.2.1))

def column (d : Data) (q : ℕ) : Fin 2 :=
  bit (QuantumSupportLookup.value (q,d.1,d.2.2))

def readPair (x : Query) : ℕ × ℕ := ((row x.2 x.1).val,(column x.2 x.1).val)

theorem bit_as_test (n : ℕ) : bit n = if n % 2 = 0 then 0 else 1 := by
  apply Fin.ext
  have hn := Nat.mod_lt n (by decide : 0 < 2)
  by_cases h : n % 2 = 0
  · simp [bit,h]
  · have he : n % 2 = 1 := by omega
    simp [bit,he]

def matrixEntry (A : Fin 2 → Fin 2 → Scalar) (x : ℕ × ℕ) : Scalar :=
  A (bit x.1) (bit x.2)

def allBits (xs : List Bool) : Bool := xs.all id

theorem fold_and (xs : List Bool) (b : Bool) :
    xs.foldl (fun a c => c && a) b = (b && xs.all id) := by
  induction xs generalizing b with
  | nil => simp
  | cons c xs ih =>
    simp only [List.foldl_cons,List.all_cons,id_eq,ih]
    cases b <;> cases c <;> rfl

end ContinuumCoulomb.QuantumHistoryBitProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDescriptors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal numeric descriptors for the actual history terms, in the exact
finite-sum order used before time grouping. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

abbrev Descriptor := ℕ × ℕ

def atIndex (work time i : ℕ) : Descriptor :=
  if i < time+1 then (0,i) else
  if i < time+1+2 then (1,i-(time+1)) else
  if i < time+1+2+(work+1) then (2,i-(time+1+2)) else
  if i < time+1+2+(work+1)+1 then (3,0) else
    (4,i-(time+1+2+(work+1)+1))

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDescriptorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial generation of the literal history-term descriptor list.  Only
the circuit's unary work count and gate-list length control enumeration. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

abbrev IndexInput := ℕ × (ℕ × ℕ)

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Natural-number formulas for the checked row sweep. These formulas keep
the same operand order and insertion point as the physical circuit. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode

def sweepIndex (width row k : ℕ) : ℕ := if row%2=0 then k else width-k

theorem sweepIndex_value (width row : ℕ) (i : Fin (width+1)) :
    (qmaSweepOrder width row i).val=sweepIndex width row i.val := by
  by_cases h : row%2=0
  · simp only [qmaSweepOrder,sweepIndex,h,ite_true, if_true,Equiv.refl_apply]
  · simp [qmaSweepOrder,sweepIndex,h,Fin.revPerm,Fin.rev]

theorem sweepIndex_inverse (width row : ℕ) (i : Fin (width+1)) :
    ((qmaSweepOrder width row).symm i).val=sweepIndex width row i.val := by
  by_cases h : row%2=0
  · simp only [qmaSweepOrder,sweepIndex,h,ite_true, if_true,Equiv.refl_symm,Equiv.refl_apply]
  · simp [qmaSweepOrder,sweepIndex,h,Fin.revPerm,Fin.rev]

def rowAddress (width row i : ℕ) : ℕ := row*(width+1)+i%(width+1)

def rowPairs (width row order : ℕ) : List (ℕ × ℕ) :=
  (List.range (width+1)).map (fun k =>
    (row*(width+1)+sweepIndex width order k,
      (row+1)*(width+1)+sweepIndex width order k))

theorem rowPairs_eq (rows width : ℕ) (row : Fin rows) (order : ℕ) :
    (qmaRowPairs (qmaGridQubit rows width row.castSucc ∘ qmaSweepOrder width order)
      (qmaGridQubit rows width row.succ ∘ qmaSweepOrder width order)).map
        (fun p => (p.1.val,p.2.val))=rowPairs width row.val order := by
  apply List.ext_getElem
  · simp only [qmaRowPairs,rowPairs,List.length_map,List.length_ofFn,List.length_range]
  · intro i hi hj
    simp only [qmaRowPairs,rowPairs,List.getElem_map,List.getElem_ofFn,List.getElem_range,
      Function.comp_apply,qmaGridQubit,Fin.val_castSucc,Fin.val_succ,sweepIndex_value]

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal arithmetic and finite lists for the alternating row sweep. The
row width is supplied in unary exactly where a list is enumerated. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram

abbrev TripleNat := ℕ × (ℕ × ℕ)

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal natural row/column tags for the sparse sweep.  The
three gates of each wire transfer carry the same column; the original gate
keeps its proved arrival column. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSweepCells
open QuantumCircuitCode

def repeatColumns (xs : List ℕ) : List ℕ := xs.flatMap (fun j => [j,j,j])

def columns (width order : ℕ) : List ℕ :=
  (List.range (width+1)).map (sweepIndex width order)

end ContinuumCoulomb.QuantumSweepCells

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

theorem patternCount_eq : patternCount=4096 := by
  norm_num [patternCount,Pattern,Fintype.card_fun]

end ContinuumCoulomb.QuantumHistoryCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary-bounded equality checks for the clock/work registers. A single
specified bit may be flipped, as required by the propagation delta. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryComparison
open ExactQuantumFactoring.BitStackProgram QuantumHistoryBitProgram

abbrev Input := ℕ × (ℕ × (Bool × (ℕ × Data)))

def point (x : Input) (k : ℕ) : Bool :=
  decide (row x.2.2.2.2 (x.2.1+k) =
    if x.2.2.1=true ∧ x.2.1+k=x.2.2.2.1 then
      Equiv.swap (0:Fin 2) 1 (column x.2.2.2.2 (x.2.1+k))
    else column x.2.2.2.2 (x.2.1+k))

def value (x : Input) : Bool := ((List.range x.1).map (point x)).all id

abbrev PointInput := Input × ℕ

theorem swap_val (b : Fin 2) : (Equiv.swap (0:Fin 2) 1 b).val=1-b.val := by
  fin_cases b <;> decide

end ContinuumCoulomb.QuantumHistoryComparison

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

def insert (a : ℕ) (xs : List ℕ) : List ℕ := if a ∈ xs then xs else a::xs

theorem insert_sublist (a : ℕ) (xs : List ℕ) : insert a xs <+ a::xs := by
  unfold insert
  split
  · exact List.sublist_cons_self _ _
  · exact List.Sublist.refl _

theorem fold_sublist (xs ys : List ℕ) :
    xs.foldl (fun zs a => insert a zs) ys <+ xs.reverse++ys := by
  induction xs generalizing ys with
  | nil => exact List.Sublist.refl _
  | cons a xs ih =>
    simp only [List.foldl_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
    exact (ih (insert a ys)).trans ((insert_sublist a ys).append_left xs.reverse)

theorem foldr_eq (xs : List ℕ) : xs.foldr insert []=xs.dedup := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.foldr_cons,ih,List.dedup_cons']
    rfl

end ContinuumCoulomb.QuantumSupportDedup

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumScalarReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reindexing of the four-rational local-core sums.  This lets the
literal support-list coordinates evaluate the propagation Gram matrix. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped BigOperators

def reindex {α β : Type} (e : α ≃ β) (A : Matrix β β Scalar) : Matrix α α Scalar :=
  fun s t => A (e s) (e t)

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRebitLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact scalar core of a lifted term with one active reference qubit.
Spectator reference bits are zero in the local core and contribute identities. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical BigOperators

def referenceState (n : ℕ) (i : Fin n) (a : Fin 2) : Fin n → Fin 2 :=
  fun j => if j=i then a else 0

def oneReference (a b : Fin 2) (z : Scalar) : Scalar :=
  add (mul (identity a b) (QuantumAlgebraicScalar.realPart z))
    (mul (neg imaginary) (mul (QuantumFixedPauli.pauli 2 a b) (imagPart z)))

end ContinuumCoulomb.QuantumAlgebraicHistory

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
open QuantumAlgebraicScalar QuantumAlgebraicHistory
open QuantumHistoryBitProgram QuantumFixedPauli
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

abbrev Input := ℕ × List ℕ

def data (n : ℕ) (s t : Fin n → Fin 2) (x : Input) : Data :=
  (x.2,List.ofFn (fun j => (s j).val),List.ofFn (fun j => (t j).val))

def table (n : ℕ) (x : Input) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) Scalar :=
  fun s t => mul (rat (1/2)) (sub (identity s t)
    (mul (QuantumFixedPauli.pauli 2 (row (data n s t x) x.1) (column (data n s t x) x.1))
      (QuantumFixedPauli.pauli 2 (row (data n s t x) (x.1+1))
        (column (data n s t x) (x.1+1)))))

theorem bit_val (b : Fin 2) : QuantumHistoryBitProgram.bit b.val=b := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt b.isLt

end ContinuumCoulomb.QuantumReferenceEdgeTable

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

local instance finDecision (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end ContinuumCoulomb.QuantumHistorySamplerProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumMergedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical merging preserves exactly the unordered endpoint support.
This includes edges whose merged coefficient is zero. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaUnorderedPair_map {α β : Type*} (f : α → β) {a b c d : α}
    (h : s(a,b) = s(c,d)) : s(f a,f b) = s(f c,f d) := by
  rcases Sym2.eq_iff.mp h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · rw [ha,hb]
  · rw [ha,hb]
    exact Sym2.eq_swap

end ContinuumCoulomb

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
open scoped Classical

theorem fin_pair_eq {n : ℕ} {a b c d : Fin n}
    (h : s(a.val,b.val) = s(c.val,d.val)) : s(a,b) = s(c,d) := by
  rcases Sym2.eq_iff.mp h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact Sym2.eq_iff.mpr (Or.inl ⟨Fin.ext ha,Fin.ext hb⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨Fin.ext ha,Fin.ext hb⟩)

end ContinuumCoulomb.QuantumPlanarTapeGeometry

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preserve the unary size bound while calling the given verifier generator.
The extra tapes hold only Boolean words; the original machine is embedded
without changing any of its instructions. -/

noncomputable section
namespace ContinuumCoulomb.QuantumUnaryPrefix
open Turing ExactQuantumFactoring.BitStackProgram

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

abbrev Tape (h : TM2ComputableInPolyTime ea eb f) := h.tm.K ⊕ Fin 3
abbrev Label (h : TM2ComputableInPolyTime ea eb f) := h.tm.Λ ⊕ Fin 7
abbrev State (h : TM2ComputableInPolyTime ea eb f) := h.tm.σ × Option Bool

def extraTapes (input saved temp : List Bool) : Fin 3 → List Bool :=
  fun i => if i=0 then input else if i=1 then saved else temp

end ContinuumCoulomb.QuantumUnaryPrefix

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryPrefixCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial time for retaining a unary size certificate around an arbitrary
Boolean-input/Boolean-output TM2 computation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumUnaryPrefix
open Turing ExactQuantumFactoring.BitStackProgram

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

def time (h : TM2ComputableInPolyTime ea eb f) : Polynomial ℕ :=
  Polynomial.C (1+2*TM2Size.programPushes h.tm)*h.time+6*Polynomial.X+7

end ContinuumCoulomb.QuantumUnaryPrefix

end

end OAI
end


