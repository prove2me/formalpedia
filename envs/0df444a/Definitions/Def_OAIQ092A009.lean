-- Prove2me | Definitions.Def_OAIQ092A009
-- name    : OAIQ092A009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T19:56:33.96759+00:00
-- url     : https://prove2.me/theorems/e88432d9-ddc3-4cb1-b9ce-a462a529a9a0
-- title:
--   Definitions bundle OAIQ092A009 of the split of OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 561 declarations of OpenAI's Lean: 444 definitions, 1 instance and 116 theorems. The definitions and types are `OAI.ContinuumCoulomb.QuantumDistinctCrossings.value`, `OAI.ContinuumCoulomb.QuantumEvenListPieces.fresh`, `OAI.ContinuumCoulomb.QuantumEvenListPieces.leafProgram`, `OAI.ContinuumCoulomb.QuantumEvenListPieces.pairList`, `OAI.ContinuumCoulomb.QuantumEvenListPieces.paths`, `OAI.ContinuumCoulomb.QuantumEvenRouteLabels.activeIndex`, `OAI.ContinuumCoulomb.QuantumEvenRouteLabels.edge`, `OAI.ContinuumCoulomb.QuantumEvenRouteLabels.edgeEquiv`, `OAI.ContinuumCoulomb.QuantumEvenRouteLabels.selectedEquiv`, `OAI.ContinuumCoulomb.QuantumEvenRouteLabels.unedge`, `OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex`, `OAI.ContinuumCoulomb.QuantumEvenRouteLabels.work`, `OAI.ContinuumCoulomb.QuantumEvenTapeGeometry.tagLeft`, `OAI.ContinuumCoulomb.QuantumEvenTapeGeometry.tagRight`, `OAI.ContinuumCoulomb.QuantumFinalRoutingProgram.inputCode`, `OAI.ContinuumCoulomb.QuantumFinalRoutingProgram.precisionProgram`, `OAI.ContinuumCoulomb.QuantumFinalRoutingProgram.spatialInputProgram`, `OAI.ContinuumCoulomb.QuantumFinalRoutingProgram.thresholdsProgram`, `OAI.ContinuumCoulomb.QuantumFiniteRouteSearch.indexProgram`, `OAI.ContinuumCoulomb.QuantumFiniteRouteSearch.selectParallelProgram`, `OAI.ContinuumCoulomb.QuantumFirstUseProgram.firstProgram`, `OAI.ContinuumCoulomb.QuantumFirstUseProgram.program`, `OAI.ContinuumCoulomb.QuantumFirstUseProgram.touchListProgram`, `OAI.ContinuumCoulomb.QuantumFixedPauli.entryProgram`, `OAI.ContinuumCoulomb.QuantumFixedPauli.matrixCode`, `OAI.ContinuumCoulomb.QuantumForkGridProgram.cellsCode`, `OAI.ContinuumCoulomb.QuantumForkGridProgram.initialCellProgram`, `OAI.ContinuumCoulomb.QuantumForkGridProgram.initialCellsCode`, `OAI.ContinuumCoulomb.QuantumForkGridProgram.initialCellsProgram`, `OAI.ContinuumCoulomb.QuantumForkGridProgram.initialQueryCode`, `OAI.ContinuumCoulomb.QuantumForkGridProgram.inputCode`, `OAI.ContinuumCoulomb.QuantumForkGridProgram.preparedCode`, `OAI.ContinuumCoulomb.QuantumForkGridProgram.queryCode`, `OAI.ContinuumCoulomb.QuantumForkList.backgroundGraph`, `OAI.ContinuumCoulomb.QuantumForkList.bondsProgram`, `OAI.ContinuumCoulomb.QuantumForkList.countProgram`, `OAI.ContinuumCoulomb.QuantumForkList.freshPointProgram`, `OAI.ContinuumCoulomb.QuantumForkList.fullGraph`, `OAI.ContinuumCoulomb.QuantumForkList.groupAtProgram`, `OAI.ContinuumCoulomb.QuantumForkList.groupsProgram` and 404 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/Computability, lean/OAI/MathematicalPhysics, in whole or in part: `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Compactness`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich`, `ContinuumCoulomb_ManyBody_FiniteBoxMatrix`, `ContinuumCoulomb_ManyBody_FiniteOneBodyCorrection`, `ContinuumCoulomb_ManyBody_FiniteWellResidual`, `ContinuumCoulomb_ManyBody_HeisenbergOffsets`, `ContinuumCoulomb_ManyBody_OrthonormalLocalizedModes`, `ContinuumCoulomb_Nuclei_DensitySynthesis`, `ContinuumCoulomb_Nuclei_FlowJetCoordinates`, `ContinuumCoulomb_Nuclei_MoserFlux`, `ContinuumCoulomb_Nuclei_MoserRegularity`, `ContinuumCoulomb_Nuclei_SlabHighAspectRatio`, `ContinuumCoulomb_Nuclei_SlabOrbitalResidual`, `ContinuumCoulomb_Nuclei_SlabRegularity`, `ContinuumCoulomb_Nuclei_SlabResidualScale`, `ContinuumCoulomb_OneParticle_CompactOrbitalDensity`, `ContinuumCoulomb_OneParticle_CompactSourceGrid`, `ContinuumCoulomb_OneParticle_ContactBaseSeparation`, `ContinuumCoulomb_OneParticle_ContactPathBounds`, `ContinuumCoulomb_OneParticle_ContactTemplates`, `ContinuumCoulomb_OneParticle_CorrectedManufacturedResidual`, `ContinuumCoulomb_OneParticle_CorrectedOneElectronProjection`, `ContinuumCoulomb_OneParticle_CoulombPoisson`, `ContinuumCoulomb_OneParticle_HoppingBox`, `ContinuumCoulomb_OneParticle_LocalizedCorrectedMatrixError`, `ContinuumCoulomb_OneParticle_LocalizedCorrectedOneBody`, `ContinuumCoulomb_OneParticle_LocalizedCoulomb`, `ContinuumCoulomb_OneParticle_LocalizedCoulombBox`, `ContinuumCoulomb_OneParticle_LocalizedCoulombMatrix`, `ContinuumCoulomb_OneParticle_LocalizedCountertermMatrix`, `ContinuumCoulomb_OneParticle_LocalizedCounterterms`, `ContinuumCoulomb_OneParticle_LocalizedDuality`, `ContinuumCoulomb_OneParticle_LocalizedFockStates`, `ContinuumCoulomb_OneParticle_LocalizedFourIndex`, `ContinuumCoulomb_OneParticle_LocalizedGram`, `ContinuumCoulomb_OneParticle_LocalizedHubbard`, `ContinuumCoulomb_OneParticle_LocalizedHubbardForm`, `ContinuumCoulomb_OneParticle_LocalizedLinearCoulomb`, `ContinuumCoulomb_OneParticle_LocalizedLinearOrbitals`, `ContinuumCoulomb_OneParticle_LocalizedModeDerivatives`, `ContinuumCoulomb_OneParticle_LocalizedModes`, `ContinuumCoulomb_OneParticle_LocalizedMultiwellResidual`, `ContinuumCoulomb_OneParticle_LocalizedOneBody`, `ContinuumCoulomb_OneParticle_LocalizedRawDensity`, `ContinuumCoulomb_OneParticle_LocalizedTensorResidual`, `ContinuumCoulomb_OneParticle_LocalizedTransition`, `ContinuumCoulomb_OneParticle_LocalizedWellMatrix`, `ContinuumCoulomb_OneParticle_LocalizedWellResidual`, `ContinuumCoulomb_OneParticle_ManufacturedGridGroundComparison`, `ContinuumCoulomb_OneParticle_ManufacturedOrbitalResidual`, `ContinuumCoulomb_OneParticle_ManufacturedSlabLower`, `ContinuumCoulomb_OneParticle_ManufacturedWeakResidual`, `ContinuumCoulomb_OneParticle_ManufacturedWellField`, `ContinuumCoulomb_OneParticle_NumericalGridRounding`, `ContinuumCoulomb_OneParticle_OrbitalCutoff`, `ContinuumCoulomb_OneParticle_OrbitalCutoffTail`, `ContinuumCoulomb_OneParticle_PlanarCutoffTail`, `ContinuumCoulomb_OneParticle_PlanarFrameBound`, `ContinuumCoulomb_OneParticle_PlanarGroundTransform`, `ContinuumCoulomb_OneParticle_PlanarModeProperties`, `ContinuumCoulomb_OneParticle_PlanarMultiwellMatrix`, `ContinuumCoulomb_OneParticle_PlanarNormalized`, `ContinuumCoulomb_OneParticle_PlanarResolventEquation`, `ContinuumCoulomb_OneParticle_PlanarSiteCutoffs`, `ContinuumCoulomb_OneParticle_PlanarWellLocalization`, `ContinuumCoulomb_OneParticle_PlanarWellMatrix`, `ContinuumCoulomb_OneParticle_RationalFieldDifferences`, `ContinuumCoulomb_OneParticle_RationalResolventError`, `ContinuumCoulomb_OneParticle_SplitCoordinates`, `ContinuumCoulomb_OneParticle_SplitFormIdentity`, `ContinuumCoulomb_OneParticle_SplitSpectralBudget`, `ContinuumCoulomb_OneParticle_SplitTestFunctions`, `ContinuumCoulomb_OneParticle_WellFieldOrbitalResidual`, `ContinuumCoulomb_Programs_EnumeratedGridNuclei`, `ContinuumCoulomb_Programs_SourceNuclearProgram`, `ContinuumCoulomb_Programs_SourcePrograms`, `ContinuumCoulomb_Programs_UnitBinaryProgram`, `ContinuumCoulomb_Quantum_QuantumCircuitPadding`, `ContinuumCoulomb_Quantum_QuantumCrossingSiteRelabel`, `ContinuumCoulomb_Quantum_QuantumCrossingsGraph`, `ContinuumCoulomb_Quantum_QuantumDescriptorSiteProgram`, `ContinuumCoulomb_Quantum_QuantumDiagonalTableProgram`, `ContinuumCoulomb_Quantum_QuantumDistinctCrossings`, `ContinuumCoulomb_Quantum_QuantumDistributedClock`, `ContinuumCoulomb_Quantum_QuantumDistributedInput`, `ContinuumCoulomb_Quantum_QuantumDistributedMatrix`, `ContinuumCoulomb_Quantum_QuantumEvenListPieces`, `ContinuumCoulomb_Quantum_QuantumEvenRouteLabels`, `ContinuumCoulomb_Quantum_QuantumEvenTapeGeometry`, `ContinuumCoulomb_Quantum_QuantumFinalRoutingProgram`, `ContinuumCoulomb_Quantum_QuantumFiniteRouteSearch`, `ContinuumCoulomb_Quantum_QuantumFirstUseProgram`, `ContinuumCoulomb_Quantum_QuantumFixedPauliProgram`, `ContinuumCoulomb_Quantum_QuantumForkGraph`, `ContinuumCoulomb_Quantum_QuantumForkGridInitial`, `ContinuumCoulomb_Quantum_QuantumForkGridProgram`, `ContinuumCoulomb_Quantum_QuantumForkListBackground`, `ContinuumCoulomb_Quantum_QuantumForkListInitialProgram`, `ContinuumCoulomb_Quantum_QuantumForkListInitialStateProgram`, `ContinuumCoulomb_Quantum_QuantumForkListPoints`, `ContinuumCoulomb_Quantum_QuantumForkListProgram`, `ContinuumCoulomb_Quantum_QuantumForkListScale`, `ContinuumCoulomb_Quantum_QuantumForkListSpatialPackage`, `ContinuumCoulomb_Quantum_QuantumForkRoutingData`, `ContinuumCoulomb_Quantum_QuantumGateArrival`, `ContinuumCoulomb_Quantum_QuantumGateEntryProgram`, `ContinuumCoulomb_Quantum_QuantumGridAcceptance`, `ContinuumCoulomb_Quantum_QuantumGridCircuit`, `ContinuumCoulomb_Quantum_QuantumGridMidpoint`, `ContinuumCoulomb_Quantum_QuantumHistory`, `ContinuumCoulomb_Quantum_QuantumHistoryBitProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryComparison`, `ContinuumCoulomb_Quantum_QuantumHistoryDeltaProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryDescriptorProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryDiagonalProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryEnergy`, `ContinuumCoulomb_Quantum_QuantumHistoryMatrix`, `ContinuumCoulomb_Quantum_QuantumHistoryPreparedProgram`, `ContinuumCoulomb_Quantum_QuantumHistorySiteProgram`, `ContinuumCoulomb_Quantum_QuantumHistorySourceProgram`, `ContinuumCoulomb_Quantum_QuantumHistoryTableProgram`, `ContinuumCoulomb_Quantum_QuantumInflatedListProgram`, `ContinuumCoulomb_Quantum_QuantumLaneUnaryProgram`, `ContinuumCoulomb_Quantum_QuantumLatticeEncoding`, `ContinuumCoulomb_Quantum_QuantumLatticeSerialization`, `ContinuumCoulomb_Quantum_QuantumListLatticeProgram`, `ContinuumCoulomb_Quantum_QuantumListMergeProgram`, `ContinuumCoulomb_Quantum_QuantumListPathProgram`, `ContinuumCoulomb_Quantum_QuantumListPathStep`, `ContinuumCoulomb_Quantum_QuantumListRouteLattice`, `ContinuumCoulomb_Quantum_QuantumListRouteProgram`, `ContinuumCoulomb_Quantum_QuantumListSchedule`, `ContinuumCoulomb_Quantum_QuantumListScheduleGeometry`, `ContinuumCoulomb_Quantum_QuantumListScheduleGraph`, `ContinuumCoulomb_Quantum_QuantumListScheduleLabels`, `ContinuumCoulomb_Quantum_QuantumListScheduleOrder`, `ContinuumCoulomb_Quantum_QuantumListScheduleProgram`, `ContinuumCoulomb_Quantum_QuantumListScheduleRealization`, `ContinuumCoulomb_Quantum_QuantumLocalPropagation`, `ContinuumCoulomb_Quantum_QuantumMappedGate`, `ContinuumCoulomb_Quantum_QuantumOrderedCellTable`, `ContinuumCoulomb_Quantum_QuantumOrderedDescriptorProgram`, `ContinuumCoulomb_Quantum_QuantumOrderedHistory`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelBlocks`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelCompile`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelEnergy`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelFamily`, `ContinuumCoulomb_Quantum_QuantumOrderedLabelProgram`, `ContinuumCoulomb_Quantum_QuantumOrderedRawPackingProgram`, `ContinuumCoulomb_Quantum_QuantumOrderedWeightProgram`, `ContinuumCoulomb_Quantum_QuantumOrdinalProgram`, `ContinuumCoulomb_Quantum_QuantumPackedSchedule`, `ContinuumCoulomb_Quantum_QuantumPaddedInput`, `ContinuumCoulomb_Quantum_QuantumPaddedLabelProgram`, `ContinuumCoulomb_Quantum_QuantumPairDedup`, `ContinuumCoulomb_Quantum_QuantumParallelRouteSearch`, `ContinuumCoulomb_Quantum_QuantumPathTable`, `ContinuumCoulomb_Quantum_QuantumPathVisitProgram`, `ContinuumCoulomb_Quantum_QuantumPathsGraph`, `ContinuumCoulomb_Quantum_QuantumPortChainProgram`, `ContinuumCoulomb_Quantum_QuantumPortRankActual`, `ContinuumCoulomb_Quantum_QuantumPortRankProgram`, `ContinuumCoulomb_Quantum_QuantumPortScheduleActual`, `ContinuumCoulomb_Quantum_QuantumPropagationSupport`, `ContinuumCoulomb_Quantum_QuantumRawFamilyProgram`, `ContinuumCoulomb_Quantum_QuantumRawProgram`, `ContinuumCoulomb_Quantum_QuantumRawSchedule`, `ContinuumCoulomb_Quantum_QuantumReferenceComparison`, `ContinuumCoulomb_Quantum_QuantumReferenceFamily`, `ContinuumCoulomb_Quantum_QuantumReferenceTerms`, `ContinuumCoulomb_Quantum_QuantumRouteLeafProgram`, `ContinuumCoulomb_Quantum_QuantumRouteSelectorProgram`, `ContinuumCoulomb_Quantum_QuantumRoutingInputProgram`, `ContinuumCoulomb_Quantum_QuantumRowInsertion`, `ContinuumCoulomb_Quantum_QuantumRowStageSupport`, `ContinuumCoulomb_Quantum_QuantumScheduleCrossingGeometry`, `ContinuumCoulomb_Quantum_QuantumSpatialCrossingProgram`, `ContinuumCoulomb_Quantum_QuantumSpatialInputTape`, `ContinuumCoulomb_Quantum_QuantumSpatialPortProgram`, `ContinuumCoulomb_Quantum_QuantumSpatialSlotProgram`, `ContinuumCoulomb_Quantum_QuantumSupportDedup`, `ContinuumCoulomb_Quantum_QuantumSupportLookup`, `ContinuumCoulomb_Quantum_QuantumSweepCellProgram`, `ContinuumCoulomb_Quantum_QuantumTaggedRouteProgram`, `ContinuumCoulomb_Quantum_QuantumTaggedSupport`, `ContinuumCoulomb_Quantum_QuantumTransferSweep`, `ContinuumCoulomb_Quantum_QuantumUnaryEmbedding`, `ContinuumCoulomb_Quantum_QuantumUnaryEnergy`, `ContinuumCoulomb_Quantum_QuantumUnaryForm`, `ContinuumCoulomb_Quantum_QuantumUnaryMatrix`, `ContinuumCoulomb_Quantum_QuantumWireGrid`, `ContinuumCoulomb_Reduction_PhysicalOneElectronLower`, `ContinuumCoulomb_Reduction_SourceGridGeometry`, `ContinuumCoulomb_Reduction_SourceNormalizedPromise`, `ContinuumCoulomb_Reduction_SourcePhysicalThreshold`, `ContinuumCoulomb_Reduction_SourcePositiveCorrectness`, `CoulombRadii_Variational_CorrectionDensity`.
--
--   **Imports.** It imports the published bundle `Def_ContinuumCoulombHardness`; the bundles `OAIQ092A004`, `OAIQ092A005`, `OAIQ092A006` and `OAIQ092A007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ092A010`, `OAIQ092A013`, `OAIQ092A014`, `OAIQ092A015`, `OAIQ092A016` and `OAIQ092A017`; the statements `OAI_ContinuumCoulomb_HubbardGlobal_actualHubbard_effectiveBottom`, `OAI.ContinuumCoulomb.ManufacturedVelocityEvaluation.approximation_error`, `OAI.ContinuumCoulomb.exists_actual_oneBody_parameters`, `OAI.ContinuumCoulomb.localized_hubbard_near_trial`, `OAI.ContinuumCoulomb.manufacturedSlab_test_lower`, `OAI.ContinuumCoulomb.manufactured_grid_witness`, `OAI.ContinuumCoulomb.manufactured_polynomial_comparison`, `OAI.ContinuumCoulomb.manufactured_uniform_nuclear_absolute_form` and `OAI_ContinuumCoulomb_publishedVerticalOscillatorGap`; the proofs of `OAI.ContinuumCoulomb.CalibratedEvaluation.scheduled_residual`, `OAI.ContinuumCoulomb.ContactCalibratedGeometry.calibrated_edge_residual`, `OAI.ContinuumCoulomb.ContactCalibratedGeometry.separation`, `OAI_ContinuumCoulomb_HubbardGlobal_actualHubbard_effectiveBottom`, `OAI.ContinuumCoulomb.ManufacturedVelocityEvaluation.approximation_error`, `OAI.ContinuumCoulomb.QuantumCrossingPacketEnergy.list_error`, `OAI.ContinuumCoulomb.binary_coulomb_qmaHard`, `OAI.ContinuumCoulomb.manufacturedSlab_test_lower`, `OAI.ContinuumCoulomb.manufactured_uniform_nuclear_absolute_form` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`.
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
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
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
import Definitions.Def_OAIQ092A004
import Definitions.Def_OAIQ092A005
import Definitions.Def_OAIQ092A006
import Definitions.Def_OAIQ092A007

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpace_solutions_1
local instance instOpensMeasurableSpace_solutions_1 : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

variable {K : Set E}

local instance instMeasurableAdd_solutions_1_re69dcf_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
/-- Extend an `L²` function on `K` by zero to a pointwise function on the ambient space. -/
def extendByZeroFun (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) : E → ℝ :=
  K.indicator fun x : E => u x

lemma hasCompactSupport_extendByZeroFun (hK : IsCompact K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    HasCompactSupport (extendByZeroFun (K := K) u) := by
  classical
  -- The indicator is pointwise supported in `K`.
  simpa [extendByZeroFun] using
    (hasCompactSupport_indicator_of_isCompact (E := E) (s := K) hK (f := fun x => u x))

/-- `extendByZeroFun` packaged as an element of `L²(volume)`. -/
noncomputable def extendByZeroL2 (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    (E →₂[(volume : Measure E)] ℝ) := by
  classical
  have hu : MeasureTheory.MemLp (fun x : E => u x) (2 : ℝ≥0∞) (volume.restrict K) :=
    MeasureTheory.Lp.memLp u
  have hm :
      MeasureTheory.MemLp (extendByZeroFun (K := K) u) (2 : ℝ≥0∞) (volume : Measure E) := by
    simpa [extendByZeroFun] using
      (MeasureTheory.memLp_indicator_iff_restrict (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
          (s := K) (f := fun x : E => u x) hKm).2 hu
  exact hm.toLp (extendByZeroFun (K := K) u)

variable (ψ : E → ℝ)

/-- Smoothing by convolution with a fixed kernel `ψ`, applied to the zero-extension from `K`. -/
def smoothFun (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) : E → ℝ :=
  (extendByZeroFun (K := K) u) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] ψ

lemma continuous_smoothFun
    (hKm : MeasurableSet K) (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    Continuous (smoothFun (K := K) ψ u) := by
  -- `extendByZeroFun u` is `L²`, hence locally integrable; convolution with a compactly supported
  -- continuous kernel is continuous.
  have hf_memLp :
      MeasureTheory.MemLp (extendByZeroFun (K := K) u)
        (2 : ℝ≥0∞) (volume : Measure E) := by
    have hu : MeasureTheory.MemLp (fun x : E => u x) (2 : ℝ≥0∞) (volume.restrict K) :=
      MeasureTheory.Lp.memLp u
    simpa [extendByZeroFun] using
      (MeasureTheory.memLp_indicator_iff_restrict (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
          (s := K) (f := fun x : E => u x) hKm).2 hu
  have hf_loc :
      MeasureTheory.LocallyIntegrable (extendByZeroFun (K := K) u)
        (volume : Measure E) := by
    have h12 : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by norm_num
    exact hf_memLp.locallyIntegrable h12
  simpa [smoothFun] using
    (hψcs.continuous_convolution_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure E)) hf_loc hψc)

lemma hasCompactSupport_smoothFun (hK : IsCompact K) (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    HasCompactSupport (smoothFun (K := K) ψ u) := by
  have hf : HasCompactSupport (extendByZeroFun (K := K) u) :=
    hasCompactSupport_extendByZeroFun (K := K) hK u
  simpa [smoothFun] using
    (hf.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure E)) hψcs)

/-- `smoothFun` packaged as an element of `L²(volume)`. -/
noncomputable def smoothL2 (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) : (E →₂[(volume : Measure E)] ℝ) :=
  let hs : HasCompactSupport (smoothFun (K := K) ψ u) :=
    hasCompactSupport_smoothFun (K := K) ψ hK hψcs u
  let hm : MeasureTheory.MemLp (smoothFun (K := K) ψ u) (2 : ℝ≥0∞) (volume : Measure E) := by
    have hc : Continuous (smoothFun (K := K) ψ u) := continuous_smoothFun (K := K) ψ hKm hψc hψcs u
    exact hc.memLp_of_hasCompactSupport (μ := (volume : Measure E)) hs
  hm.toLp (smoothFun (K := K) ψ u)

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
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Compactness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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
# `L²` compactness criterion: compact smoothing operator (Euclidean)

This file proves the compactness of the fixed-kernel smoothing operator used in the
Fréchet–Kolmogorov / Riesz–Kolmogorov approach to Euclidean Rellich–Kondrachov.

## Main results

- `Kψ`: the compact set `K + tsupport ψ` controlling supports of smoothed functions.
- `smoothBCF`: `smoothFun` packaged as a `BoundedContinuousFunction` on `Kψ`.
- `uniformContinuous_ψ`: `UniformContinuous ψ` from `Continuous ψ` + `HasCompactSupport ψ`.

The Arzelà–Ascoli compactness statement for `smoothBCF` lives in
`RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.ArzelaAscoli`.

This is tracked under Beads `lean-103.5.2.26.5.3.2.2.1`.
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

variable {K : Set E}
variable {ψ : E → ℝ}

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceE_L2CompactnessCompactness
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceE_L2CompactnessCompactness
local instance instOpensMeasurableSpaceE_L2CompactnessCompactness_re69dcf_1 : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableAddE_L2CompactnessCompactness_re69dcf_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNegE_L2CompactnessCompactness_re69dcf_1 : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
def smoothOn (hKm : MeasurableSet K) (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    C(↥(Kψ (K := K) (ψ := ψ)), ℝ) where
  toFun x := smoothFun (E := E) (K := K) ψ u x
  continuous_toFun := by
    have : Continuous (smoothFun (E := E) (K := K) ψ u) :=
      continuous_smoothFun (E := E) (K := K) (ψ := ψ) (hKm := hKm) hψc hψcs u
    exact this.comp continuous_subtype_val

/-- `smoothFun` packaged as a `BoundedContinuousFunction` on the compact set `K + tsupport ψ`. -/
def smoothBCF (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ :=
  letI : CompactSpace ↥(Kψ (K := K) (ψ := ψ)) :=
    isCompact_iff_compactSpace.1 (isCompact_Kψ (K := K) (ψ := ψ) hK hψcs)
  BoundedContinuousFunction.mkOfCompact (smoothOn (E := E) (K := K) (ψ := ψ) hKm hψc hψcs u)

@[simp] lemma smoothBCF_apply (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
    (x : ↥(Kψ (K := K) (ψ := ψ))) :
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x =
      smoothFun (E := E) (K := K) ψ u x := by
  rfl

/-!
The remainder of the compactness proof (Arzelà–Ascoli on the family `smoothBCF '' closedBall`)
is tracked as part of `lean-103.5.2.26.5.3.2.2.1`.

We intentionally keep the helper lemmas above in this file so the final proof can stay short and
only reference re-usable bounds.
-/

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

/-! ### Supported `H¹` subspace -/

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceE_SobolevEuclideanRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceE_SobolevEuclideanRellich
local instance instOpensMeasurableSpaceE_SobolevEuclideanRellich_re69dcf_1 : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableAddE_SobolevEuclideanRellich_re69dcf_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNegE_SobolevEuclideanRellich_re69dcf_1 : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instFactOneLeTwo_SobolevEuclideanRellich
/-- The inclusion `h1On K → L²(volume)` as a continuous linear map. -/
noncomputable def h1OnToL2 (K : Set E) (hKm : MeasurableSet K) :
    ↥(h1On K hKm) →L[ℝ] (E →₂[(volume : Measure E)] ℝ) :=
  (h1ToL2 (μ := (volume : Measure E)) (E := E)).comp (h1On K hKm).subtypeL

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPoisson
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Coulomb fundamental solution with finite smoothness

The manufactured planar well in the unit-charge paper has bounded continuous
derivatives through a finite order. Its density synthesis therefore needs
the fundamental-solution identity for compactly supported C² functions.
This extends the smooth-test identity by the same regularized
kernel argument, using only two integrations by parts.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace ContinuumCoulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

def manufacturedCharge (V : Position → ℝ) (x : Position) : ℝ :=
  coordinateLaplacian V x / (4 * Real.pi)

end ContinuumCoulomb

end

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

def planarLaplacian (f : PlanarPosition → ℝ) (x : PlanarPosition) : ℝ :=
  ∑ a : Fin 2, planarPartial (planarPartial f (planarAxis a)) (planarAxis a) x

def planarTestForm (W u : PlanarPosition → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∑ a : Fin 2, ∫ x, planarPartial u (planarAxis a) x ^ 2) +
    ∫ x, W x * u x ^ 2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeProperties
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

theorem normalizedPlanarMode_C7 : ContDiff ℝ 7 normalizedPlanarMode :=
  planarResolventMode_C7.div_const _

theorem normalizedPlanarMode_positive (r : PlanarPosition) : 0 < normalizedPlanarMode r :=
  div_pos (planarResolventMode_positive r) (Real.sqrt_pos.mpr planarResolventMode_square_integral_positive)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarResolventEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The differential eigen-equation of the constructed resolvent mode is
obtained from its heat representation and the fundamental theorem of calculus,
not supplied as an assumption. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

def planarHeatResolventDerivative (r : PlanarPosition) (t : ℝ) : ℝ :=
  Real.exp (-t) * (∫ b, planarHeatKernel t b * planarLaplacian planarForcing (r - b)) -
    Real.exp (-t) * planarHeatAverage t r

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarNormalized
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem planarPartial_const_mul {f : PlanarPosition → ℝ} (hf : ContDiff ℝ 1 f)
    (c : ℝ) (e r : PlanarPosition) :
    planarPartial (fun x => c * f x) e r = c * planarPartial f e r := by
  unfold planarPartial
  rw [fderiv_const_mul (hf.differentiable (by norm_num) r) c]
  rfl

theorem normalizedPlanarMode_square_integrable :
    Integrable (fun r => normalizedPlanarMode r ^ 2) := by
  simp_rw [normalizedPlanarMode, div_pow]
  exact planarResolventMode_square_integrable.div_const _

theorem normalizedPlanarMode_memLp : MemLp normalizedPlanarMode 2 :=
  (memLp_two_iff_integrable_sq normalizedPlanarMode_C7.continuous.aestronglyMeasurable).mpr
    normalizedPlanarMode_square_integrable

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedModes
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual localized modes in planar/transverse coordinates. The measure is
the product of planar Euclidean volume and one-dimensional Lebesgue measure.
The split Laplacian below is the sum of the three coordinate derivatives. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedPotential (freq : ℝ) (u : PlanarPosition) (p : SplitPosition) : ℝ :=
  manufacturedPlanarWell (p.1 - u) + freq ^ 2 * p.2 ^ 2 / 2

def splitLaplacian (f : SplitPosition → ℝ) (p : SplitPosition) : ℝ :=
  planarLaplacian (fun r => f (r, p.2)) p.1 +
    deriv (deriv (fun z => f (p.1, z))) p.2

theorem localizedMode_C7 (freq : ℝ) (u : PlanarPosition) :
    ContDiff ℝ 7 (localizedMode freq u) :=
  (normalizedPlanarMode_C7.comp (contDiff_fst.sub contDiff_const)).mul
    (((verticalMode_smooth freq).of_le (by first | simp | exact_mod_cast le_top)).comp contDiff_snd)

theorem localizedMode_positive {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (p : SplitPosition) : 0 < localizedMode freq u p :=
  mul_pos (normalizedPlanarMode_positive _) (verticalMode_positive hfreq _)

theorem localizedMode_square_integrable {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : Integrable (fun p => localizedMode freq u p ^ 2) := by
  simp_rw [localizedMode, mul_pow]
  exact (normalizedPlanarMode_square_integrable.comp_sub_right u).mul_prod
    (verticalMode_square_integrable hfreq)

theorem localizedMode_memLp {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    MemLp (localizedMode freq u) 2 :=
  (memLp_two_iff_integrable_sq (localizedMode_C7 freq u).continuous.aestronglyMeasurable).mpr
    (localizedMode_square_integrable hfreq u)

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

theorem continuumLocalizedMode_C7 (freq : ℝ) (u : PlanarPosition) :
    ContDiff ℝ 7 (continuumLocalizedMode freq u) :=
  (localizedMode_C7 freq u).comp positionSplitCoordinates.contDiff

theorem continuumLocalizedMode_positive {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) : 0 < continuumLocalizedMode freq u x :=
  localizedMode_positive hfreq u _

theorem continuumLocalizedMode_memLp {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    MemLp (continuumLocalizedMode freq u) 2 :=
  (localizedMode_memLp hfreq u).comp_measurePreserving positionSplitCoordinates_measurePreserving

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Variational_CorrectionDensity
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

theorem potentialOf_lipschitz_bound {ρ : Position → ℝ} {A : ℝ}
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x) (hA : ∀ x, ρ x ≤ A) (x x' : Position) :
    ‖potentialOf ρ x-potentialOf ρ x'‖ ≤
      (A*(∫ y in Metric.ball (0 : Position) 1, (coulombKernel y)^2)+(∫ y, ρ y))*‖x-x'‖ := by
  have hi (z : Position) : Integrable (fun y => coulombKernel (z-y)*ρ y) :=
    (bounded_density_convolution measurable_coulombKernel coulombKernel_nonneg
      (coulombKernel_integrableOn_ball 1) (fun _ => coulombKernel_le_one)
      hρ hpos hA z).1
  have hb (z : Position) := bounded_density_convolution
    (measurable_coulombKernel.pow_const 2) (fun y => sq_nonneg (coulombKernel y))
    (coulombKernel_sq_integrableOn_ball 1)
    (fun y hy => by nlinarith [coulombKernel_le_one hy, coulombKernel_nonneg y])
    hρ hpos hA z
  have hdomi : Integrable (fun y => ‖x-x'‖/2*
      ((coulombKernel (x-y))^2*ρ y+(coulombKernel (x'-y))^2*ρ y)) :=
    ((hb x).1.add (hb x').1).const_mul (‖x-x'‖/2)
  have hdom : ∀ᵐ y : Position ∂volume,
      ‖coulombKernel (x-y)*ρ y-coulombKernel (x'-y)*ρ y‖ ≤
        ‖x-x'‖/2*((coulombKernel (x-y))^2*ρ y+(coulombKernel (x'-y))^2*ρ y) := by
    filter_upwards [volume.ae_ne x, volume.ae_ne x'] with y hy hy'
    rw [← sub_mul, norm_mul, Real.norm_eq_abs (ρ y), abs_of_nonneg (hpos y)]
    have hh := mul_le_mul_of_nonneg_right
      (coulombKernel_sub_le (sub_ne_zero.mpr hy.symm) (sub_ne_zero.mpr hy'.symm)) (hpos y)
    simpa only [sub_sub_sub_cancel_right, Real.norm_eq_abs, mul_add, add_mul, mul_assoc] using hh
  have hh := norm_integral_le_of_norm_le hdomi hdom
  rw [integral_sub (hi x) (hi x'), integral_const_mul,
    integral_add (hb x).1 (hb x').1] at hh
  refine hh.trans ?_
  have hh' := add_le_add (hb x).2 (hb x').2
  nlinarith [mul_le_mul_of_nonneg_left hh' (norm_nonneg (x-x'))]

theorem potentialOf_lipschitz {ρ : Position → ℝ} {A : ℝ}
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x) (hA : ∀ x, ρ x ≤ A) :
    ∃ C : NNReal, LipschitzWith C (potentialOf ρ) := by
  let B := A*(∫ y in Metric.ball (0 : Position) 1, (coulombKernel y)^2)+(∫ y, ρ y)
  have hB : 0 ≤ B := by
    exact add_nonneg (mul_nonneg ((hpos 0).trans (hA 0))
      (integral_nonneg (fun y => sq_nonneg _))) (integral_nonneg hpos)
  exact ⟨⟨B,hB⟩, lipschitzWith_iff_norm_sub_le.mpr (potentialOf_lipschitz_bound hρ hpos hA)⟩

theorem potentialOf_continuous {ρ : Position → ℝ} {A : ℝ}
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x) (hA : ∀ x, ρ x ≤ A) :
    Continuous (potentialOf ρ) :=
  (potentialOf_lipschitz hρ hpos hA).choose_spec.continuous

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

theorem localizedAmplitudeBound_positive {freq : ℝ} (hfreq : 0 < freq) :
    0 < localizedAmplitudeBound freq :=
  mul_pos (one_div_pos.mpr (Real.sqrt_pos.mpr planarResolventMode_square_integral_positive))
    (one_div_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (div_pos Real.pi_pos hfreq))))

theorem continuumLocalizedMode_le {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) :
    continuumLocalizedMode freq u x ≤ localizedAmplitudeBound freq := by
  have hp (r : PlanarPosition) : normalizedPlanarMode r ≤
      1 / Real.sqrt (∫ s, planarResolventMode s ^ 2) :=
    div_le_div_of_nonneg_right (planarResolventMode_le_one r) (Real.sqrt_nonneg _)
  have hv (z : ℝ) : verticalMode freq z ≤ 1 / Real.sqrt (Real.sqrt (Real.pi / freq)) := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z])
  exact mul_le_mul (hp _) (hv _) (verticalMode_positive hfreq _).le
    (by positivity)

theorem localizedDensity_continuous (freq : ℝ) (u : PlanarPosition) :
    Continuous (localizedDensity freq u) := (continuumLocalizedMode_C7 freq u).continuous.pow 2

theorem localizedDensity_integrable {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    Integrable (localizedDensity freq u) :=
  (memLp_two_iff_integrable_sq (continuumLocalizedMode_C7 freq u).continuous.aestronglyMeasurable).mp
    (continuumLocalizedMode_memLp hfreq u)

theorem localizedDensity_bound {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) :
    localizedDensity freq u x ≤ localizedAmplitudeBound freq ^ 2 :=
  (sq_le_sq₀ (continuumLocalizedMode_positive hfreq u x).le
    (localizedAmplitudeBound_positive hfreq).le).mpr (continuumLocalizedMode_le hfreq u x)

end ContinuumCoulomb

end

end OAI
end

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

theorem normalizedPlanarMode_partial (e r : PlanarPosition) :
    planarPartial normalizedPlanarMode e r =
      (Real.sqrt (∫ s, planarResolventMode s ^ 2))⁻¹ * planarPartial planarResolventMode e r := by
  rw [normalizedPlanarMode_eq_const_mul, planarPartial_const_mul
    (planarResolventMode_C7.of_le (by norm_num))]

theorem localizedMode_fderiv (freq : ℝ) (u : PlanarPosition) (p e : SplitPosition) :
    fderiv ℝ (localizedMode freq u) p e =
      planarPartial normalizedPlanarMode e.1 (p.1 - u) * verticalMode freq p.2 +
        normalizedPlanarMode (p.1 - u) * deriv (verticalMode freq) p.2 * e.2 := by
  have hp := (normalizedPlanarMode_C7.differentiable (by norm_num) (p.1 - u)).hasFDerivAt.comp p
    (hasFDerivAt_fst.sub_const u)
  have hv := (verticalMode_hasDerivAt freq p.2).hasFDerivAt.comp p hasFDerivAt_snd
  have h := congrArg (fun L : SplitPosition →L[ℝ] ℝ => L e) (hp.mul hv).fderiv
  have hfun : (fun q : SplitPosition => normalizedPlanarMode (q.1 - u) * verticalMode freq q.2) =
      localizedMode freq u := rfl
  have hh : fderiv ℝ (fun q : SplitPosition => normalizedPlanarMode (q.1 - u) * verticalMode freq q.2) p e =
      normalizedPlanarMode (p.1 - u) * (e.2 * (-freq * p.2 * verticalMode freq p.2)) +
        verticalMode freq p.2 * fderiv ℝ normalizedPlanarMode (p.1 - u) e.1 := by
    simpa only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.toSpanSingleton_apply, Function.comp_def, Pi.mul_def] using h
  rw [hfun] at hh
  rw [verticalMode_deriv]
  unfold planarPartial
  nlinarith only [hh]

theorem localizedMode_verticalDerivative_memLp {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    MemLp (fun p : SplitPosition => normalizedPlanarMode (p.1 - u) * deriv (verticalMode freq) p.2) 2 := by
  apply (memLp_two_iff_integrable_sq (by
    exact ((normalizedPlanarMode_C7.continuous.comp (continuous_fst.sub continuous_const)).mul
      (((verticalMode_smooth freq).continuous_deriv (by simp)).comp continuous_snd)).aestronglyMeasurable)).mpr
  simp_rw [mul_pow]
  rw [Measure.volume_eq_prod]
  exact (normalizedPlanarMode_square_integrable.comp_sub_right u).mul_prod
    (verticalMode_deriv_square_integrable hfreq)

theorem continuumLocalizedMode_fderiv (freq : ℝ) (u : PlanarPosition) (x e : Position) :
    fderiv ℝ (continuumLocalizedMode freq u) x e =
      fderiv ℝ (localizedMode freq u) (positionSplitCoordinates x) (positionSplitCoordinates e) := by
  have h := ((localizedMode_C7 freq u).differentiable (by norm_num) (positionSplitCoordinates x)).hasFDerivAt.comp x
    positionSplitCoordinates.hasFDerivAt
  exact congrArg (fun L : Position →L[ℝ] ℝ => L e) h.fderiv

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

def synthesizedDensity (rho H S : ℝ) (V : Position → ℝ) (x : Position) : ℝ :=
  slabDensity rho H S x + manufacturedCharge V x

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

theorem localizedTransition_continuous (freq : ℝ) (u v : PlanarPosition) :
    Continuous (localizedTransition freq u v) :=
  (continuumLocalizedMode_C7 freq u).continuous.mul (continuumLocalizedMode_C7 freq v).continuous

theorem localizedTransition_nonnegative {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) (x : Position) : 0 ≤ localizedTransition freq u v x :=
  mul_nonneg (continuumLocalizedMode_positive hfreq u x).le (continuumLocalizedMode_positive hfreq v x).le

theorem localizedTransition_integrable {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    Integrable (localizedTransition freq u v) :=
  (continuumLocalizedMode_memLp hfreq u).integrable_mul (continuumLocalizedMode_memLp hfreq v)

theorem localizedTransition_bound {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) (x : Position) :
    localizedTransition freq u v x ≤ localizedAmplitudeBound freq ^ 2 := by
  have h := mul_le_mul (continuumLocalizedMode_le hfreq u x) (continuumLocalizedMode_le hfreq v x)
    (continuumLocalizedMode_positive hfreq v x).le (localizedAmplitudeBound_positive hfreq).le
  simpa only [localizedTransition, pow_two] using h

def localizedTransitionPacket {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) : CoulombPacket where
  value := localizedTransition freq u v
  continuous := localizedTransition_continuous freq u v
  integrable := localizedTransition_integrable hfreq u v
  bound := localizedAmplitudeBound freq ^ 2
  bound_nonnegative := sq_nonneg _
  bound_spec x := by
    rw [Real.norm_of_nonneg (localizedTransition_nonnegative hfreq u v x)]
    exact localizedTransition_bound hfreq u v x

end ContinuumCoulomb

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

def localizedFourIndex (freq : ℝ) (u v w z : PlanarPosition) : ℝ :=
  ∫ x, localizedTransition freq u v x * NeutralAtom.potentialOf (localizedTransition freq w z) x

def localizedFourIndexConstant (freq : ℝ) : ℝ := localizedPotentialBound freq * planarOverlapConstant

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarWellMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual well matrix elements. The well at the first orbital center gives
exactly the distance-dependent hopping; a well far from both centers gives
an error decaying at rate 1.9. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarWellMatrix (u v w : PlanarPosition) : ℝ :=
  ∫ r, normalizedPlanarMode (r - u) * manufacturedPlanarWell (r - w) * normalizedPlanarMode (r - v)

def planarWellMatrixConstant : ℝ :=
  normalizedPlanarExponentialConstant (19 / 20) ^ 2 * Real.exp (19 / 10) *
    (∫ r : PlanarPosition, |manufacturedPlanarWell r|)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedDuality
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual compact local dual tests: a common positive diagonal mass,
disjoint supports and exponentially small off-site pairings. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

def localizedTest (χ : Position → ℝ) (u : PlanarPosition) (x : Position) : ℝ :=
  χ (x - planarCenter u)

def localizedDualPair (freq : ℝ) (u v : PlanarPosition) (χ : Position → ℝ) : ℝ :=
  ∫ x, localizedDensity freq u x * localizedTest χ v x

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

def localizedPacket {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) : CoulombPacket where
  value := localizedDensity freq u
  continuous := localizedDensity_continuous freq u
  integrable := localizedDensity_integrable hfreq u
  bound := localizedAmplitudeBound freq ^ 2
  bound_nonnegative := sq_nonneg _
  bound_spec x := by
    rw [Real.norm_of_nonneg (localizedDensity_nonnegative freq u x)]
    exact localizedDensity_bound hfreq u x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCounterterms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's actual well-depth counterterms: direct Coulomb sums
divided by the fixed positive onsite well integral. Their diagonal action
cancels the required linear occupancy term exactly. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def localizedOffsiteSum (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) : ℝ :=
  ∑ j, if i = j then 0 else localizedCoulombCoeff freq (u i) (u j)

def localizedCounterterm (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) : ℝ :=
  localizedOffsiteSum freq u i / planarHopping 0

def localizedCountertermBound (freq : ℝ) : ℝ := localizedPotentialBound freq / planarHopping 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarSiteCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual scaled cutoffs for separated planar sites. Their square
partition has a localization cost of order D⁻² independent of site count. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb
open PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

def planarSiteAngle (D : ℝ) (u x : PlanarPosition) : ℝ :=
  (Real.pi / 2) * cutoffBump ((6 / D) • (x - u))

def planarSitePartition {ι : Type*} [Fintype ι] (D : ℝ) (u : ι → PlanarPosition) :
    Option ι → PlanarPosition → ℝ := planarTrigPartition (fun i => planarSiteAngle D (u i))

def planarSiteDerivativeBound (D : ℝ) : ℝ :=
  (Real.pi / 2 * (6 / D)) * cutoffGradBound

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarWellLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact localization of the actual sum of manufactured wells. Site
pieces see exactly their own well; the exterior piece sees zero potential. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def planarWellSum {ι : Type*} [Fintype ι] (u : ι → PlanarPosition) (x : PlanarPosition) : ℝ :=
  ∑ i, manufacturedPlanarWell (x-u i)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedWellField
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

def countertermWellSum (freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (r : PlanarPosition) : ℝ :=
  ∑ i, (1 + localizedCounterterm freq u i / scale) * manufacturedPlanarWell (r-u i)

def manufacturedWellField (freq scale S : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (x : Position) : ℝ :=
  slabWellCutoff S (positionSplitCoordinates x).2 *
    countertermWellSum freq scale u (positionSplitCoordinates x).1

theorem countertermWellSum_C7 (freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) :
    ContDiff ℝ 7 (countertermWellSum freq scale u) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (manufacturedPlanarWell_C7.comp (contDiff_id.sub contDiff_const))

theorem manufacturedWellField_C7 (freq scale S : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) : ContDiff ℝ 7 (manufacturedWellField freq scale S u) :=
  ((slabWellCutoff_smooth S).of_le (by first | simp | exact_mod_cast le_top) |>.comp
    positionSplitCoordinates.contDiff.snd).mul
    ((countertermWellSum_C7 freq scale u).comp positionSplitCoordinates.contDiff.fst)

end ContinuumCoulomb

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

def orbitalCutoff (R : ℝ) (u : PlanarPosition) (x : Position) : ℝ :=
  orbitalCutoffBump (R⁻¹ • (x-planarCenter u))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OrbitalCutoffTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative Sobolev tails of the localized orbitals. The 24th
moments give a twelfth-power decay in the H1 norm of the removed tail. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

def orbitalRemainder (freq R : ℝ) (u : PlanarPosition) (x : Position) : ℝ :=
  (1-orbitalCutoff R u x)*continuumLocalizedMode freq u x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_WellFieldOrbitalResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cutoff and depth-counterterm contribution to the actual localized
one-particle residual. The estimate uses polynomially many spatial modes. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def wellFieldOrbitalResidual (freq scale S : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) (x : Position) : ℝ :=
  (manufacturedWellField freq scale S u x-planarWellSum u (positionSplitCoordinates x).1)*
    continuumLocalizedMode freq (u j) x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteWellResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite vertical cutoff error after retaining the intended well-depth
counterterms. Its bound decays with the slab height and does not include the
counterterm itself as an error. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def finiteWellOrbitalResidual (freq scale S : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) (x : Position) : ℝ :=
  (manufacturedWellField freq scale S u x-countertermWellSum freq scale u (positionSplitCoordinates x).1)*
    continuumLocalizedMode freq (u j) x

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

def planarSiteCutoffError (D : ℝ) (u x : PlanarPosition) : ℝ :=
  (Real.sin (planarSiteAngle D u x) - 1) * normalizedPlanarMode (x-u)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarFrameBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual uncut planar modes satisfy the finite-frame bound needed
when combining planar and transverse spectral estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def planarOrbitalL2 (u : PlanarPosition) : Lp ℝ 2 (volume : Measure PlanarPosition) :=
  (normalizedPlanarMode_memLp.comp_measurePreserving
    (measurePreserving_sub_right volume u)).toLp (fun r => normalizedPlanarMode (r-u))

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

def splitPlanarForm {m : ℕ} (u : Fin m → PlanarPosition) (f : SplitPosition → ℝ) : ℝ :=
  ∫ z, planarTestForm (planarWellSum u) (fun r => f (r,z))

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

def splitPlanarPartial (f : SplitPosition → ℝ) (a : Fin 2) (p : SplitPosition) : ℝ :=
  fderiv ℝ f p (planarAxis a,0)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitFormIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini identities for the full split-coordinate kinetic and potential
forms. No domain restriction beyond compact C1 test functions is introduced. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def splitRealKinetic (f : SplitPosition → ℝ) : ℝ :=
  (1/2:ℝ)*((∑ a : Fin 2, ∫ p, (splitPlanarPartial f a p)^2) +
    ∫ p, (splitVerticalPartial f p)^2)

def splitRealForm (V : SplitPosition → ℝ) (f : SplitPosition → ℝ) : ℝ :=
  splitRealKinetic f+∫ p, V p*f p^2

def splitSeparablePotential {m : ℕ} (u : Fin m → PlanarPosition)
    (freq S : ℝ) (p : SplitPosition) : ℝ :=
  planarWellSum u p.1+verticalCapPotential freq S p.2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedSlabLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global comparison of the actual manufactured Coulomb field with the
separable capped oscillator and planar wells. -/

noncomputable section
namespace ContinuumCoulomb

def manufacturedSlabPotential (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (x : Position) : ℝ :=
  slabPotential rho H S x-slabPotential rho H S 0+manufacturedWellField freq scale S u x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabRegularity
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

theorem slabPotential_eq_negativePotentialOf (rho H S : ℝ) :
    slabPotential rho H S = fun x => -NeutralAtom.potentialOf (slabDensity rho H S) x := rfl

theorem slabPotential_continuous {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) : Continuous (slabPotential rho H S) := by
  rw [slabPotential_eq_negativePotentialOf]
  exact (NeutralAtom.potentialOf_continuous (slabDensity_integrable hH hS rho)
    (slabDensity_nonnegative hrho H S) (slabDensity_le hrho H S)).neg

theorem manufacturedSlabPotential_continuous {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (freq scale : ℝ)
    {m : ℕ} (u : Fin m → PlanarPosition) :
    Continuous (manufacturedSlabPotential rho H S freq scale u) :=
  ((slabPotential_continuous hrho hH hS).sub continuous_const).add
    (manufacturedWellField_C7 freq scale S u).continuous

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

def slabUniformBound (rho H S : ℝ) : ℝ :=
  rho*NeutralAtom.kernelBallMass 1+volume.real (slabDomain H S)*rho

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCountertermMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual counterterm matrix estimates: the onsite term is the required
negative direct-interaction sum; other diagonal terms have two tails and
off-diagonal terms have the actual overlap decay. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def localizedCountertermMatrix (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) : ℝ :=
  ∑ k, localizedCounterterm freq u k * planarWellMatrix (u i) (u j) (u k)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedWellMatrix
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual three-dimensional well matrix elements equal the planar ones:
the transverse Gaussian contributes exactly its unit squared mass. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedWellIntegrand (freq : ℝ) (u v w : PlanarPosition) (x : Position) : ℝ :=
  continuumLocalizedMode freq u x * manufacturedPlanarWell ((positionSplitCoordinates x).1 - w) *
    continuumLocalizedMode freq v x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarMultiwellMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unperturbed shifted multiwell matrix: its leading off-diagonal
entry is the actual hopping, and every remaining term has two tail factors.
No independent matrix approximation is assumed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def planarMultiwellMatrix {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) : ℝ :=
  ∑ k, if k = j then 0 else planarWellMatrix (u i) (u j) (u k)

def planarHoppingMatrix {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) : ℝ :=
  if i = j then 0 else -planarHopping ‖u i - u j‖

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedOneBody
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual differential action of the full multiwell operator on the
localized modes. Subtraction of the common ground energy leaves exactly the
sum of other wells, so its matrix is the checked hopping matrix plus the
explicit two-tail error. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def multiwellPotential (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (p : SplitPosition) : ℝ :=
  (∑ k, manufacturedPlanarWell (p.1 - u k)) + freq ^ 2 * p.2 ^ 2 / 2

def multiwellAction (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (f : SplitPosition → ℝ) (p : SplitPosition) : ℝ :=
  -(1 / 2 : ℝ) * splitLaplacian f p + multiwellPotential freq u p * f p

def localizedOneBodyIntegrand (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (i j : Fin m) (x : Position) : ℝ :=
  continuumLocalizedMode freq (u i) x *
    (multiwellAction freq u (localizedMode freq (u j)) (positionSplitCoordinates x) -
      ((-1 / 2 : ℝ) + freq / 2) * continuumLocalizedMode freq (u j) x)

def localizedOneBodyMatrix (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) : ℝ :=
  ∫ x, localizedOneBodyIntegrand freq u i j x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCorrectedOneBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual one-body operator including well-depth counterterms. Its
shifted matrix is exactly the base multiwell matrix plus the weighted well
matrix divided by the physical scale. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def correctedMultiwellAction (freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (f : SplitPosition → ℝ) (p : SplitPosition) : ℝ :=
  multiwellAction freq u f p + scale⁻¹ *
    (∑ k, localizedCounterterm freq u k * manufacturedPlanarWell (p.1 - u k)) * f p

def localizedCorrectedOneBodyIntegrand (freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (i j : Fin m) (x : Position) : ℝ :=
  continuumLocalizedMode freq (u i) x *
    (correctedMultiwellAction freq scale u (localizedMode freq (u j)) (positionSplitCoordinates x) -
      ((-1 / 2 : ℝ) + freq / 2) * continuumLocalizedMode freq (u j) x)

def localizedCorrectedOneBodyMatrix (freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) : ℝ :=
  ∫ x, localizedCorrectedOneBodyIntegrand freq scale u i j x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedWellResidual
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual other-well residual has exponentially small L2 mass.
The square of a nonpositive bounded well is controlled by its negative
well matrix element, so the checked two-tail estimate applies directly. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedWellAction (freq : ℝ) (u w : PlanarPosition) (x : Position) : ℝ :=
  manufacturedPlanarWell ((positionSplitCoordinates x).1-w) * continuumLocalizedMode freq u x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedMultiwellResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L2 bounds on the actual differential residuals of the localized modes.
The estimate is polynomial in the number of wells; it does not sum over a
many-electron occupation basis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def localizedMultiwellResidual (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) (x : Position) : ℝ :=
  ∑ k, if k = j then 0 else localizedWellAction freq (u j) (u k) x

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

def manufacturedOrbitalResidual (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) (x : Position) : ℝ :=
  localizedMultiwellResidual freq u j x+slabOrbitalResidual rho H S freq (u j) x+
    wellFieldOrbitalResidual freq scale S u j x

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

def finiteBoxOrbitalResidual (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) (x : Position) : ℝ :=
  slabOrbitalResidual rho H S freq (u j) x+finiteWellOrbitalResidual freq scale S u j x

def manufacturedRawOneBodyMatrix (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i j : Fin m) : ℝ :=
  ∫ x, continuumLocalizedMode freq (u i) x*manufacturedOrbitalResidual rho H S freq scale u j x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedLinearOrbitals
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem localizedLinearOrbital_C7 (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (a : Fin m → ℝ) : ContDiff ℝ 7 (localizedLinearOrbital freq u a) :=
  ContDiff.sum (fun j _ => contDiff_const.mul (continuumLocalizedMode_C7 freq (u j)))

theorem localizedLinearOrbital_memLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a : Fin m → ℝ) :
    MemLp (localizedLinearOrbital freq u a) 2 := by
  have ht (j : Fin m) : MemLp (fun x => a j * continuumLocalizedMode freq (u j) x) 2 volume :=
    (continuumLocalizedMode_memLp hfreq (u j)).const_mul (a j)
  exact memLp_finsetSum Finset.univ (fun j _ => ht j)

theorem localizedLinearOrbital_fderiv (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (a : Fin m → ℝ) (x e : Position) :
    fderiv ℝ (localizedLinearOrbital freq u a) x e =
      ∑ j, a j * fderiv ℝ (continuumLocalizedMode freq (u j)) x e := by
  have hd (j : Fin m) : DifferentiableAt ℝ (continuumLocalizedMode freq (u j)) x :=
    (continuumLocalizedMode_C7 freq (u j)).differentiable (by norm_num) x
  unfold localizedLinearOrbital
  rw [fderiv_fun_sum (fun j _ => (hd j).const_mul _)]
  simp only [sum_apply, fderiv_const_mul (hd _), smul_apply, smul_eq_mul]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_OrthonormalLocalizedModes
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem correctedLocalizedMode_C1 (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) :
    ContDiff ℝ 1 (correctedLocalizedMode freq u i) :=
  (localizedLinearOrbital_C7 freq u _).of_le (by norm_num)

theorem correctedLocalizedMode_memLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) : MemLp (correctedLocalizedMode freq u i) 2 :=
  localizedLinearOrbital_memLp hfreq u _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CorrectedManufacturedResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram correction preserves a polynomial residual bound: it sums over
spatial modes, independently of the many-electron occupation basis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def correctedManufacturedResidual (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) (x : Position) : ℝ :=
  ∑ j, correctedLocalizedCoefficients u i j*manufacturedOrbitalResidual rho H S freq scale u j x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserFlux
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit density homotopy and continuity equation used to transport
uniform slab density in the unit-charge construction. The identities describe
the explicit field and its density homotopy. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

def homotopyDensity (rho : ℝ) (V : Position → ℝ) (t : ℝ) (x : Position) : ℝ :=
  rho + t * manufacturedCharge V x

def moserVelocity (rho : ℝ) (V : Position → ℝ) (t : ℝ) (x : Position) : Position :=
  WithLp.toLp 2 (fun a => -(dirPartial V (axis a) x) /
    (4 * Real.pi * homotopyDensity rho V t x))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_MoserRegularity
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite C⁶ regularity of the manufactured well gives the C⁴ transport
field required by the unit-charge cubature. No C∞ assumption is added. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

def moserDomain (rho : ℝ) (V : Position → ℝ) : Set (ℝ × Position) :=
  {p | homotopyDensity rho V p.1 p.2 ≠ 0}

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CompactOrbitalDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact cutoff densities for compressed nuclear matrix elements. The
fourth-order source bounds grow only cubically in the cutoff radius. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def compactOrbitalDensity (freq R : ℝ) (u v : PlanarPosition) (x : Position) : ℝ :=
  orbitalCutoff R u x*(continuumLocalizedMode freq u x*continuumLocalizedMode freq v x)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CompactSourceGrid
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fourth-order cell error for a compact orbital source, split into
cells near that source or the transport support and the remaining far cells. -/

noncomputable section
open MeasureTheory
open scoped Classical
namespace ContinuumCoulomb

def sourceExceptionalCell (E : Set Position) (u : PlanarPosition) (R : ℝ)
    (b : Position) (h : ℝ) : Prop :=
  (∃ x ∈ positionCube b h, x ∈ E) ∨ ‖planarCenter u-b‖ ≤ 4*R

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCorrectedMatrixError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative comparison of the actual shifted and scaled one-body
matrix with the hopping and Coulomb occupancy counterterm matrix. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def localizedOneBodyTarget (scale freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (i j : Fin m) : ℝ :=
  scale * planarHoppingMatrix u i j - if i=j then localizedOffsiteSum freq u i else 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteOneBodyCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual corrected one-body matrix entries, including the singular nuclear
error. Finite change of basis preserves the quantitative entrywise estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def correctedManufacturedOneBodyMatrix (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i j : Fin m) : ℝ :=
  ∫ x, correctedLocalizedMode freq u i x*correctedManufacturedResidual rho H S freq scale u j x

def correctedNuclearOneBodyMatrix (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (F : Position → ℝ) (i j : Fin m) : ℝ :=
  correctedManufacturedOneBodyMatrix rho H S freq scale u i j+
    ∫ x, F x*correctedLocalizedMode freq u i x*correctedLocalizedMode freq u j x

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

def finiteHeisenbergBottom (n : ℕ) (left right : Edge → Fin n) (J : Edge → ℝ) : ℝ :=
  sourceMatrixBottom n (finiteHeisenbergMatrix n left right J)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowJetCoordinates
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
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

def spatialJetCoordinates (n : ℕ) :
    SpatialJet n →ₗ[ℝ] ((Fin n → Fin 3) → Position) where
  toFun A e := A (fun i => NeutralAtom.axis (e i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabResidualScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial choice of slab dimensions makes the actual orbital
residual small. The twenty-fourth moment absorbs the total slab mass. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def slabGrowthConstant (rho : ℝ) : ℝ :=
  rho*(|NeutralAtom.kernelBallMass 1|+8)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabHighAspectRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A slab aspect ratio compatible with the nuclear cubature scale.
The 72nd value moment permits horizontal radius T^10 at height T. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def slabResidualSeventySecondBound (rho freq : ℝ) (u : PlanarPosition) : ℝ :=
  72*Real.pi^2*rho^2+8192*rho^2*localizedDensityMoment freq u 4+
    8*(slabGrowthConstant rho)^2*localizedDensityMoment freq u 72+
    8*Real.pi^2*rho^2*localizedDensityMoment freq u 72

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactTemplates
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem contactPathVertex_end (c : ℝ) :
    contactPathVertex c 9 = contactPoint (5 + 4 * c) 0 := by
  ext i
  fin_cases i
  · norm_num [contactPathVertex, contactPoint, Finset.sum_range_succ, contactStepX]
    ring
  · norm_num [contactPathVertex, contactPoint, Finset.sum_range_succ, contactStepY]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactPathBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem contactPath_transverse_bounds {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    {k : ℕ} (hk : k ≤ 9) :
    0 ≤ contactPathVertex c k 1 ∧ contactPathVertex c k 1 ≤ 4 / 3 := by
  have hs := contactSlopeHeight_bounds hc hc'
  interval_cases k <;> norm_num [contactPathVertex, Finset.sum_range_succ, contactStepY,
    contactPoint] <;> (try constructor) <;> linarith

theorem contactPath_axial_bounds {c : ℝ} (hc : 3 / 4 ≤ c) (_hc' : c ≤ 7 / 8)
    {k : ℕ} (hk : k ≤ 9) :
    0 ≤ contactPathVertex c k 0 ∧ contactPathVertex c k 0 ≤ 5 + 4 * c := by
  interval_cases k <;> norm_num [contactPathVertex, Finset.sum_range_succ, contactStepX,
    contactPoint] <;> (try constructor) <;> linarith

theorem contactPath_internal_axial_bounds {c : ℝ} (hc : 3 / 4 ≤ c) (_hc' : c ≤ 7 / 8)
    {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 8) :
    1 ≤ contactPathVertex c k 0 ∧ contactPathVertex c k 0 ≤ 4 + 4 * c := by
  interval_cases k <;> norm_num [contactPathVertex, Finset.sum_range_succ, contactStepX,
    contactPoint] <;> (try constructor) <;> linarith

theorem contactPath_off_axis_bounds {c : ℝ} (hc : 3 / 4 ≤ c) (_hc' : c ≤ 7 / 8)
    {k : ℕ} (hk : k ≤ 9) (hy : contactPathVertex c k 1 ≠ 0) :
    11 / 4 ≤ contactPathVertex c k 0 ∧ contactPathVertex c k 0 ≤ 9 / 4 + 4 * c := by
  interval_cases k <;> norm_num [contactPathVertex, Finset.sum_range_succ, contactStepY, contactPoint] at hy
  all_goals norm_num [contactPathVertex, Finset.sum_range_succ, contactStepX, contactPoint]
  all_goals constructor <;> linarith

/-- Left-path internal sites and its central endpoint satisfy the common
length-17 strip bounds. -/
def leftContactStripSite (c : ℝ) (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 9) : ContactStripSite where
  axial := contactPathVertex c k 0
  transverse := contactPathVertex c k 1
  axial_lower := by
    by_cases h : k = 9
    · subst k
      rw [contactPathVertex_end, contactPoint_zero]
      linarith
    · exact (contactPath_internal_axial_bounds hc hc' hk (by omega)).1
  axial_upper := (contactPath_axial_bounds hc hc' hk').2.trans (by linarith)
  transverse_lower := (contactPath_transverse_bounds hc hc' hk').1
  transverse_upper := (contactPath_transverse_bounds hc hc' hk').2
  off_axis_lower := fun h => (contactPath_off_axis_bounds hc hc' hk' h).1
  off_axis_upper := fun h => (contactPath_off_axis_bounds hc hc' hk' h).2.trans (by linarith)

/-- Right-path internal sites use an origin chosen so their far endpoint is17. -/
def rightContactStripSite (c origin : ℝ) (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (horigin : origin + (5 + 4 * c) = 17)
    (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 8) : ContactStripSite where
  axial := origin + contactPathVertex c k 0
  transverse := contactPathVertex c k 1
  axial_lower := by
    have := (contactPath_internal_axial_bounds hc hc' hk hk').1
    linarith
  axial_upper := by
    have := (contactPath_internal_axial_bounds hc hc' hk hk').2
    linarith
  transverse_lower := (contactPath_transverse_bounds hc hc' (by omega : k ≤ 9)).1
  transverse_upper := (contactPath_transverse_bounds hc hc' (by omega : k ≤ 9)).2
  off_axis_lower := by
    intro hy
    have := (contactPath_off_axis_bounds hc hc' (by omega : k ≤ 9) hy).1
    linarith
  off_axis_upper := by
    intro hy
    have := (contactPath_off_axis_bounds hc hc' (by omega : k ≤ 9) hy).2
    linarith

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

def contactBaseGadgetPosition (negative : Bool) : ContactGadgetSite → ContactPoint :=
  Sum.elim (fun k => contactPathVertex (contactGadgetSlope negative) k.val)
    (Sum.elim (fun k => contactPoint (contactGadgetRightOrigin negative 1) 0 +
      contactPathVertex (contactGadgetSlope negative) (k.val + 1))
      (fun _ => if negative then contactPoint (17 / 2) 1 else contactPoint 9 0))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CorrectedOneElectronProjection
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem lifted_corrected_mode_C1 (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) :
    ContDiff ℝ 1 (fun x : Configuration 1 =>
      (correctedLocalizedMode freq u i (oneElectronCoordinates x) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp ((correctedLocalizedMode_C1 freq u i).comp
    oneElectronCoordinates.contDiff)

theorem lifted_corrected_mode_partial (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) (x : Configuration 1) (b : Fin 3) :
    fderiv ℝ (fun y : Configuration 1 =>
      (correctedLocalizedMode freq u i (oneElectronCoordinates y) : ℂ)) x
        (EuclideanSpace.single (0,b) 1) =
      (fderiv ℝ (correctedLocalizedMode freq u i) (oneElectronCoordinates x)
        (EuclideanSpace.single b 1) : ℂ) := by
  have hr := ((correctedLocalizedMode_C1 freq u i).differentiable (by norm_num)
    (oneElectronCoordinates x)).hasFDerivAt.comp x
      oneElectronCoordinates.toContinuousLinearEquiv.hasFDerivAt
  have h := congrArg (fun L : Configuration 1 →L[ℝ] ℂ =>
    L (EuclideanSpace.single (0,b) 1)) (Complex.ofRealCLM.hasFDerivAt.comp x hr).fderiv
  simpa only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    oneElectronCoordinates_single, Function.comp_def] using h

theorem correctedOneElectronValue_C1 (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (c : SpinConfiguration 1 → Fin m → ℂ) (s : SpinConfiguration 1) :
    ContDiff ℝ 1 (correctedOneElectronValue freq u c s) :=
  ContDiff.sum (fun i _ => contDiff_const.mul (lifted_corrected_mode_C1 freq u i))

theorem correctedOneElectronValue_memLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (c : SpinConfiguration 1 → Fin m → ℂ)
    (s : SpinConfiguration 1) : MemLp (correctedOneElectronValue freq u c s) 2 :=
  memLp_finsetSum Finset.univ (fun i _ =>
    ((correctedLocalizedMode_memLp hfreq u i).ofReal.comp_measurePreserving
      oneElectronCoordinates.measurePreserving).const_mul (c s i))

theorem correctedOneElectronValue_partial (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (c : SpinConfiguration 1 → Fin m → ℂ)
    (s : SpinConfiguration 1) (x : Configuration 1) (b : Fin 3) :
    fderiv ℝ (correctedOneElectronValue freq u c s) x (EuclideanSpace.single (0,b) 1) =
      ∑ i, c s i*(fderiv ℝ (correctedLocalizedMode freq u i) (oneElectronCoordinates x)
        (EuclideanSpace.single b 1) : ℂ) := by
  have hd (i : Fin m) := (lifted_corrected_mode_C1 freq u i).differentiable (by norm_num) x
  unfold correctedOneElectronValue
  rw [fderiv_fun_sum (fun i _ => (hd i).const_mul (c s i))]
  simp only [sum_apply, fderiv_const_mul (hd _),
    smul_apply, smul_eq_mul, lifted_corrected_mode_partial]

def correctedOneElectronCoefficients {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (v : Coulomb.H1Vector 1)
    (s : SpinConfiguration 1) (i : Fin m) : ℂ :=
  inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
    (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v (Sum.inl s))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_HoppingBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual contact numerator is an integral over the fixed forcing
square. Its translated sample point is represented exactly by rational
subtraction, so the concrete resolvent evaluator applies directly. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarHoppingNumerator (d : ℝ) : ℝ := ∫ r, planarHoppingIntegrand d r

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombBox
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual direct coefficient is approximated by a bounded integral
on a six-dimensional rational cube. The cap and truncation errors are
uniform in the relative displacement of the two fixed density packets. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedCappedProfile (freq ε : ℝ) (u : PlanarPosition) : ℝ :=
  ∫ p, cappedPairIntegrand ε (planarCenter u)
    (localizedDensity freq 0) (localizedDensity freq 0) p

def localizedCoulombBoxIntegral (freq ε L : ℝ) (u : PlanarPosition) : ℝ :=
  ∫ p in coulombNumericalBox L ×ˢ coulombNumericalBox L,
    cappedPairIntegrand ε (planarCenter u)
      (localizedDensity freq 0) (localizedDensity freq 0) p

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedWeakResidual
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.complexMollification_im _root_.OAI.ContinuumCoulomb.complexMollification_re _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem oneElectronLocalizedMode_C2 (freq : ℝ) (u : PlanarPosition) :
    ContDiff ℝ 2 (oneElectronLocalizedMode freq u) :=
  ((continuumLocalizedMode_C7 freq u).of_le (by norm_num)).comp oneElectronCoordinates.contDiff

theorem oneElectronLocalizedMode_partial (freq : ℝ) (u : PlanarPosition)
    (a : Fin 1 × Fin 3) (x : Configuration 1) :
    configurationRealPartial (oneElectronLocalizedMode freq u) a x =
      fderiv ℝ (continuumLocalizedMode freq u) (oneElectronCoordinates x)
        (oneElectronCoordinates (EuclideanSpace.single a 1)) := by
  exact congrArg (fun L : Configuration 1 →L[ℝ] ℝ => L (EuclideanSpace.single a 1))
    (((continuumLocalizedMode_C7 freq u).differentiable (by norm_num) _).hasFDerivAt.comp x
      oneElectronCoordinates.toContinuousLinearEquiv.hasFDerivAt).fderiv

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

theorem localizedSpinMode_C1 (freq : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (j : Fin ((2*m+1)+1)) (s : Fin 2) : ContDiff ℝ 1 (fun x => localizedSpinMode freq u j x s) :=
  realSpinOrbital_C1 _ (correctedLocalizedMode_C1 freq u _) _ s

theorem localizedSpinMode_memLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (j : Fin ((2*m+1)+1)) (s : Fin 2) :
    MemLp (fun x => localizedSpinMode freq u j x s) 2 :=
  realSpinOrbital_memLp _ (correctedLocalizedMode_memLp hfreq u _) _ s

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedLinearCoulomb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coulomb integrals of actual linear combinations of the localized
orbitals. Bounded-L1 packets make the full four-index change of basis an
exact identity, with joint singular-kernel integrability. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def localizedLinearTransitionPacket {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a b : Fin m → ℝ) : CoulombPacket :=
  CoulombPacket.combination
    (fun j => CoulombPacket.combination (fun k => localizedTransitionPacket hfreq (u j) (u k))
      (fun k => a j * b k)) (fun _ => 1)

def localizedLinearFourIndex {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a b c d : Fin m → ℝ) : ℝ :=
  CoulombPacket.pair (localizedLinearTransitionPacket hfreq u a b)
    (localizedLinearTransitionPacket hfreq u c d)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual corrected spatial-spin Coulomb tensor differs from its
occupation-diagonal density interaction by the Gram and off-site errors. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def localizedDensityTensor (freq : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (a b c d : Fin ((2*m+1)+1)) : ℂ :=
  let p := (HubbardGlobal.siteModes m).symm
  if a=c ∧ b=d then
    (localizedFourIndex freq (u (p a).1) (u (p a).1) (u (p b).1) (u (p b).1):ℂ) else 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedHubbard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual localized direct Coulomb matrix satisfies the full charge
penalty condition used by the complete half-filled Hubbard comparison. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def localizedOffsiteCoulomb {m : ℕ} (freq : ℝ) (u : Fin m → PlanarPosition)
    (i j : Fin m) : ℝ := if i = j then 0 else localizedCoulombCoeff freq (u i) (u j)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedTensorResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual corrected manufactured orbital residuals, lifted to both spin
components and all electron coordinates, satisfy a polynomial L2 estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def localizedSpinResidual (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (j : Fin ((2*m+1)+1)) : Position → Fin 2 → ℂ :=
  realSpinOrbital (correctedManufacturedResidual rho H S freq scale u
    ((HubbardGlobal.siteModes m).symm j).1) ((HubbardGlobal.siteModes m).symm j).2

end ContinuumCoulomb

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

def planarSpectralLevel (γ : ℝ) (m : ℕ) (D η : ℝ) : ℝ :=
  -1/2+γ-planarSiteDerivativeBound D^2-
    γ*(1+η⁻¹)*m*planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8))

def physicalSeparablePotential {m : ℕ} (u : Fin m → PlanarPosition)
    (freq S : ℝ) (x : Position) : ℝ :=
  splitSeparablePotential u freq S (positionSplitCoordinates x)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedHubbardForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual manufactured continuum form on its localized tensor space
is controlled by the full half-filled Hubbard variational problem. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal Laughlin.Fock

def localizedHubbardFormError (m : ℕ) (freq D ε : ℝ) : ℝ :=
  (2*m+1+1:ℝ)^2*ε+(1/2:ℝ)*(2*m+1+1:ℝ)^4*
    ((m+1:ℝ)^4*(32*(2*(m+1:ℝ)*localizedOverlapBound D)*localizedPotentialBound freq)+
      localizedFourIndexConstant freq*Real.exp (-(9/10:ℝ)*D))

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

def localizedRawCoulombBox (freq ε L : ℝ) (u : PlanarPosition) : ℝ :=
  ∫ p in coulombNumericalBox L ×ˢ coulombNumericalBox L,
    cappedPairIntegrand ε (planarCenter u) (localizedRawDensity freq) (localizedRawDensity freq) p

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedGridGroundComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual transported unit-charge cloud has two-sided physical ground
bounds obtained from the full-domain lower estimate and localized trials. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal

def manufacturedGridError {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ)
    (G : Position → Position) (rho H S freq scale h : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (y : Position) : ℝ :=
  gridNuclearPotential index G rho h y-(slabPotential rho H S y+manufacturedWellField freq scale S u y)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalFieldDifferences
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
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

theorem position_injective : Function.Injective position := by
  rintro ⟨a,ay,az⟩ ⟨b,byCoord,bz⟩ h
  have h0 := congrArg (fun x : Position => x 0) h
  have h1 := congrArg (fun x : Position => x 1) h
  have h2 := congrArg (fun x : Position => x 2) h
  change (a:ℝ) = (b:ℝ) at h0
  change (ay:ℝ) = (byCoord:ℝ) at h1
  change (az:ℝ) = (bz:ℝ) at h2
  have h0' : a=b := by exact_mod_cast h0
  have h1' : ay=byCoord := by exact_mod_cast h1
  have h2' : az=bz := by exact_mod_cast h2
  simp only [h0',h1',h2']

def extend (V : Position → ℝ) (sample : Triple → ℚ) (x : Position) : ℝ := by
  classical
  exact if h : ∃ q, position q=x then (sample (Classical.choose h):ℝ) else V x

end ContinuumCoulomb.RationalFieldDifferences

end

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

def planeErrorBound (e : Settings) (η : ℝ) : ℝ :=
  4 * (2 * planarBoxSpatialConstant (PlanarForcingProgram.position e.2.1) η *
    (spatialStep e.2.2 : ℝ) +
    ((2 ^ e.1.2.1 : ℝ)⁻¹ + 8 / (e.1.2.2 : ℝ)) / (4 * η))

def resolventErrorBound (x : Input) : ℝ :=
  (x.1 : ℝ) * (4 * planarBoxTimeConstant (PlanarForcingProgram.position x.2.1.2.1)
    (x.2.2.1 : ℝ) * (x.2.2.2 : ℝ) ^ 2 +
    (x.2.2.2 : ℝ) * planeErrorBound x.2.1 (x.2.2.1 : ℝ)) +
    (x.2.2.1 : ℝ) + Real.exp (-(timeEndpoint x : ℝ))

end ContinuumCoulomb.RationalHeatBox

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_EnumeratedGridNuclei
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

instance centeredGridIndices_nonempty (r : Fin 3 → ℕ) :
    Nonempty {k // k ∈ centeredGridIndices r} :=
  ⟨⟨0,(mem_centeredGridIndices r 0).mpr (fun i => by simp)⟩⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_NumericalGridRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of the full ground-energy interval to the actual rational
Euler/Gauss nodes, with the physical inverse-scale coordinates. -/

noncomputable section
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb
open CappedKernelProgram (Triple position)

def physicalRationalNuclei {m : ℕ} (hm : 0 < m) (q : Fin m → Triple)
    (hq : Function.Injective q) {scale : ℝ} (hs : 0 < scale) : Coulomb.Nuclei m where
  nonempty := hm
  position a := scale⁻¹ • position (q a)
  distinct := by
    intro a b hab
    apply hq
    apply RationalFieldDifferences.position_injective
    have he := congrArg (fun x : Position => scale • x) hab
    simpa only [smul_inv_smul₀ hs.ne'] using he
  charge _ := 1
  charge_ge_one _ := le_rfl

end ContinuumCoulomb

end

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

noncomputable def upper : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => d.upper.value) := rationalValue.comp ((Procedure.second _ _).comp thresholdTuple)

end ContinuumCoulomb.SourcePrograms

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

noncomputable opaque positionSplitter : PrefixPrograms.Splitter binaryPositionCodec :=
  SourcePrograms.equivSplitter _ binaryPositionEquiv
    (PrefixPrograms.pair _ _ SourcePrograms.rationalSplitter
      (PrefixPrograms.pair _ _ SourcePrograms.rationalSplitter SourcePrograms.rationalSplitter))

noncomputable opaque positionListSplitter : PrefixPrograms.Splitter positionListCodec :=
  PrefixListPrograms.listSplitter binaryPositionCodec positionSplitter zeroPosition position_length_pos

noncomputable opaque inputTuple : Procedure unitCoulombCodec.encode
    (prodCode positionListCodec.encode tailCodec.encode) unitCoulombEquiv :=
  (SourcePrograms.pairInput positionListCodec tailCodec positionListSplitter).precompose unitCoulombEquiv

noncomputable opaque positionsRaw : Procedure unitCoulombCodec.encode positionListCodec.encode
    UnitCoulomb.nuclei := (Procedure.first _ _).comp inputTuple
noncomputable opaque tailRaw : Procedure unitCoulombCodec.encode tailCodec.encode
    (fun d => (d.electrons, d.lower, d.upper)) := (Procedure.second _ _).comp inputTuple
noncomputable opaque positions : Procedure unitCoulombCodec.encode (listCode binaryPositionCodec.encode)
    UnitCoulomb.nuclei :=
  (PrefixListPrograms.listInput binaryPositionCodec positionSplitter zeroPosition position_length_pos).comp positionsRaw

noncomputable opaque attachOne : Procedure binaryPositionCodec.encode nucleusCodec.encode
    (fun r => (r, 1)) :=
  (EncodingPrograms.appendPair binaryPositionCodec BinaryEncoding.natural).comp
    ((Procedure.identity binaryPositionCodec.encode).pair
      (Procedure.constant binaryPositionCodec.encode BinaryEncoding.natural.encode 1))

noncomputable opaque nuclei : Procedure unitCoulombCodec.encode nucleusListCodec.encode
    (fun d => d.nuclei.map (fun r => (r, 1))) :=
  (PrefixListPrograms.listOutput nucleusCodec (zeroPosition, 1)).comp
    ((Procedure.listMap zeroPosition (zeroPosition, 1) attachOne).comp positions)

noncomputable opaque program : Procedure unitCoulombCodec.encode binaryCoulombCodec.encode
    UnitCoulomb.toBinary :=
  ((EncodingPrograms.appendPair nucleusListCodec tailCodec).comp (nuclei.pair tailRaw)).result
    (by intro d; rfl)

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

def positiveEnergy (d : SquareLatticeHeisenberg) (W G : ℕ) : ℝ :=
  sourceMatrixBottom _
    (MediatorIteration.finalGraph (family d (denominator d.edges G))
      (denominator d.edges G + W + 1) G).matrix

end ContinuumCoulomb.SourceNormalizedSpectrum

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

def energy (x : Registers) : ℝ := sourceMatrixBottom x.vertices (SourceBondLists.matrix x.vertices x.bonds)

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

noncomputable opaque tauProgram (B : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => (((SourceContactProgram.size d^(30*B):ℕ):ℚ)⁻¹)) :=
  Procedure.ratInv.comp (Procedure.natToRat.comp
    (Procedure.unaryToBits.comp (SourceContactProgram.powerProgram (30*B))))

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

noncomputable opaque amplificationProgram (rho k : ℕ) :
    Procedure binaryHeisenbergCodec.encode ratCode (amplification rho k) := by
  let n := Procedure.natToRat.comp
    (Procedure.unaryToBits.comp (SourceContactProgram.powerProgram (10*k)))
  let n2 := Procedure.ratMul.comp (n.pair n)
  let n3 := Procedure.ratMul.comp (n2.pair n)
  let num := Procedure.ratMul.comp
    ((Procedure.constant binaryHeisenbergCodec.encode ratCode 8).pair n3)
  exact (Procedure.ratDiv.comp (num.pair
    (Procedure.constant binaryHeisenbergCodec.encode ratCode (rho:ℚ)))).congrFun (by
      intro d
      change (8*((((SourceContactProgram.size d^(10*k):ℕ):ℚ)*
          ((SourceContactProgram.size d^(10*k):ℕ):ℚ))*
          ((SourceContactProgram.size d^(10*k):ℕ):ℚ)))/(rho:ℚ) = _
      simp only [amplification,CenteredPhysicalThreshold.amplification,SourcePhysicalThreshold.mesh]
      ring)

noncomputable opaque verticalProgram (k : ℕ) :
    Procedure binaryHeisenbergCodec.encode ratCode (SourcePhysicalThreshold.slabVertical k) := by
  let m := Procedure.natToRat.comp
    (Procedure.unaryToBits.comp (SourceContactProgram.powerProgram (10*k)))
  let s := Procedure.natToRat.comp
    (Procedure.unaryToBits.comp (SourceContactProgram.powerProgram (15*k)))
  let num := Procedure.ratAdd.comp
    (s.pair (Procedure.constant binaryHeisenbergCodec.encode ratCode (1/2:ℚ)))
  exact (Procedure.ratDiv.comp (num.pair m)).congrFun (by intro d; rfl)

end ContinuumCoulomb.SourceNuclearProgram

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

def qmaPropagationEnergy (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) : ℝ :=
  ∑ t ∈ Finset.range c.gates.length, ‖u (t+1)-qmaApplyMatrix (qmaStepMatrix c t) (u t)‖^2

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

def qmaHistoryEnergy (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) : ℝ :=
  qmaOutputPenalty c u+7*qmaInputPenalty c u+
    8*c.gates.length*qmaPropagationEnergy c u

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite Hermitian circuit-history Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaPropagationMap (c : QMACircuit) :
    (QMAHistoryBasis c → ℂ) →ₗ[ℂ] (QMAPropagationBasis c → ℂ) where
  toFun u ts :=
    u (⟨ts.1.val+1,Nat.succ_lt_succ ts.1.isLt⟩,ts.2)-
    (qmaStepMatrix c ts.1.val).mulVec
      (fun s => u (⟨ts.1.val,ts.1.isLt.trans (Nat.lt_succ_self _)⟩,s)) ts.2
  map_add' u v := by
    funext ts
    change (u _+v _)-(qmaStepMatrix c ts.1.val).mulVec
      ((fun s => u (⟨ts.1.val,ts.1.isLt.trans (Nat.lt_succ_self _)⟩,s))+
       (fun s => v (⟨ts.1.val,ts.1.isLt.trans (Nat.lt_succ_self _)⟩,s))) ts.2 = _
    rw [Matrix.mulVec_add]
    simp only [Pi.add_apply]
    ring
  map_smul' a u := by
    funext ts
    change a*u _-(qmaStepMatrix c ts.1.val).mulVec
      (a • (fun s => u (⟨ts.1.val,ts.1.isLt.trans (Nat.lt_succ_self _)⟩,s))) ts.2 = _
    rw [Matrix.mulVec_smul]
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

def qmaPropagationMatrix (c : QMACircuit) :
    Matrix (QMAPropagationBasis c) (QMAHistoryBasis c) ℂ :=
  LinearMap.toMatrix' (qmaPropagationMap c)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full unary-clock form retains every clock configuration. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaUnaryRestrict (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) : QMAHistoryBasis c → ℂ :=
  fun p => u (qmaHistoryClock c.gates.length p.1,p.2)

def qmaUnaryMass (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) : ℝ :=
  ∑ p, Complex.normSq (u p)

def qmaUnaryInvalidMass (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) : ℝ :=
  ∑ s : SourceSpinBasis (c.gates.length+2),
    if QMALegalClock c.gates.length s then 0 else ∑ a, Complex.normSq (u (s,a))

def qmaUnaryClockEnergy (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) : ℝ :=
  ∑ s : SourceSpinBasis (c.gates.length+2),
    qmaPinnedClockPenalty c.gates.length s * ∑ a, Complex.normSq (u (s,a))

def qmaUnaryResidual (c : QMACircuit) (u : QMAUnaryBasis c → ℂ)
    (t : Fin c.gates.length) (s : SourceSpinBasis (c.gates.length+2)) :
    SourceSpinBasis (c.work+1) → ℂ :=
  fun a => u (Function.update s (qmaClockMiddle c.gates.length t) 1,a)-
    (qmaStepMatrix c t.val).mulVec (fun b => u (s,b)) a

def qmaUnaryPropagationEnergy (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) : ℝ :=
  ∑ t : Fin c.gates.length, ∑ s : SourceSpinBasis (c.gates.length+2),
    if QMAClockGuard c.gates.length t s ∧ s (qmaClockMiddle c.gates.length t) = 0 then
      ∑ a, Complex.normSq (qmaUnaryResidual c u t s a) else 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local endpoint penalties dominate the finite history penalties. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaUnaryOutputEnergy (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) : ℝ :=
  ∑ s : SourceSpinBasis (c.gates.length+2), if s (qmaOutputMarker c) = 1 then
    ∑ a : SourceSpinBasis (c.work+1), if a (Fin.last c.work) ≠ 1 then
      Complex.normSq (u (s,a)) else 0 else 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isometric embedding of the finite history into all unary clock strings. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaUnaryInclusion (c : QMACircuit) (p : QMAHistoryBasis c) : QMAUnaryBasis c :=
  (qmaHistoryClock c.gates.length p.1,p.2)

def qmaUnaryExtend (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) : QMAUnaryBasis c → ℂ :=
  Function.extend (qmaUnaryInclusion c) u (fun _ => 0)

end ContinuumCoulomb

end

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

def qmaUnaryClockDiagonal (c : QMACircuit) (p : QMAUnaryBasis c) : ℝ :=
  qmaPinnedClockPenalty c.gates.length p.1

def qmaUnaryOutputDiagonal (c : QMACircuit) (p : QMAUnaryBasis c) : ℝ :=
  if p.1 (qmaOutputMarker c) = 1 ∧ p.2 (Fin.last c.work) ≠ 1 then 1 else 0

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

def qmaCircuitQubitSplit (c : QMACircuit) :
    (QMACircuitQubit c → Fin 2) ≃ QMAUnaryBasis c :=
  Equiv.sumArrowEquivProdArrow _ _ _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input checks may occur at separate history times before their qubits are changed. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaDistributedInput (c : QMACircuit) (τ : Fin (c.work+1) → ℕ)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) : ℝ :=
  ∑ i : Fin (c.work+1), ‖qmaMask (qmaInputCheck c i) (u (τ i))‖^2

def qmaDistributedHistoryEnergy (c : QMACircuit) (τ : Fin (c.work+1) → ℕ)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) : ℝ :=
  qmaOutputPenalty c u+14*qmaDistributedInput c τ u+
    (14*(c.work+1)+8)*c.gates.length*qmaPropagationEnergy c u

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTransferSweep
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem qmaTransferGates_wellFormed {work : ℕ} (ps : List (Fin (work+1) × Fin (work+1)))
    (hp : ∀ p ∈ ps, p.1 ≠ p.2) :
    ∀ g ∈ qmaTransferGates ps, g.WellFormed (work+1) := by
  induction ps with
  | nil => simp [qmaTransferGates]
  | cons p ps ih =>
    rcases p with ⟨i,j⟩
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact qmaWireSwapGates_wellFormed i j (hp (i,j) (by simp)) g hg
    · exact ih (fun p h => hp p (by simp [h])) g hg

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedClock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local initialization checks at arbitrary unary-clock positions. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaUnaryDistributedInput (c : QMACircuit) (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (u : QMAUnaryBasis c → ℂ) : ℝ :=
  ∑ i : Fin (c.work+1), ∑ s : SourceSpinBasis (c.gates.length+2),
    if qmaClockAt c.gates.length (τ i) s then
      ∑ a : SourceSpinBasis (c.work+1), if qmaInputCheck c i a then
        Complex.normSq (u (s,a)) else 0 else 0

def qmaUnaryDistributedEnergy (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (u : QMAUnaryBasis c → ℂ) : ℝ :=
  qmaUnaryClockEnergy c u+qmaUnaryOutputEnergy c u+14*qmaUnaryDistributedInput c τ u+
    (14*(c.work+1)+8)*c.gates.length*qmaUnaryPropagationEnergy c u

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

def qmaUnaryDistributedDiagonal (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (p : QMAUnaryBasis c) : ℝ :=
  ∑ i : Fin (c.work+1), if qmaClockAt c.gates.length (τ i) p.1 ∧
    qmaInputCheck c i p.2 then 1 else 0

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

def qmaGridTransfer (rows width : ℕ) (r : Fin rows) : List QMAGate :=
  qmaTransferGates (qmaRowPairs (qmaGridQubit rows width r.castSucc)
    (qmaGridQubit rows width r.succ))

theorem qmaGridTransfer_wellFormed (rows width : ℕ) (r : Fin rows) :
    ∀ g ∈ qmaGridTransfer rows width r, g.WellFormed (qmaGridWork rows width+1) := by
  apply qmaTransferGates_wellFormed
  apply qmaRowPairs_distinct
  exact qmaGridRows_disjoint rows width r.castSucc r.succ (qmaGridRow_ne rows r)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumMappedGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit gate addresses for a logical register embedded in a larger wire grid. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaMapGate_wellFormed (sourceWork targetWork : ℕ)
    (f : Fin (sourceWork+1) → Fin (targetWork+1)) (hf : Function.Injective f)
    (g : QMAGate) (hg : g.WellFormed (sourceWork+1)) :
    (qmaMapGate sourceWork targetWork f g).WellFormed (targetWork+1) := by
  cases g with
  | hadamard i => exact (f (qmaQubit sourceWork i)).isLt
  | phaseT i => exact (f (qmaQubit sourceWork i)).isLt
  | controlledNot i j =>
    refine ⟨(f (qmaQubit sourceWork i)).isLt,(f (qmaQubit sourceWork j)).isLt,?_⟩
    intro he
    have h := congrArg Fin.val (hf (Fin.ext he))
    simp only [qmaQubit,Nat.mod_eq_of_lt hg.1,Nat.mod_eq_of_lt hg.2.1] at h
    exact hg.2.2 h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridCircuit
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete circuit that transfers its full active register to a fresh row per gate. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

def qmaGridCircuitFrom (rows width : ℕ) :
    (start : ℕ) → (gs : List QMAGate) → start+gs.length ≤ rows → List QMAGate
  | _,[],_ => []
  | start,g::gs,h =>
      qmaGridTransfer rows width ⟨start,by simp only [List.length_cons] at h; omega⟩ ++
      [qmaMapGate width (qmaGridWork rows width)
        (qmaGridQubit rows width ⟨start+1,by simp only [List.length_cons] at h; omega⟩) g] ++
      qmaGridCircuitFrom rows width (start+1) gs (by simp only [List.length_cons] at h; omega)

theorem qmaGridCircuitFrom_wellFormed (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) (hg : ∀ g ∈ gs, g.WellFormed (width+1)) :
    ∀ g ∈ qmaGridCircuitFrom rows width start gs h,
      g.WellFormed (qmaGridWork rows width+1) := by
  induction gs generalizing start with
  | nil => simp [qmaGridCircuitFrom]
  | cons g gs ih =>
    intro k hk
    have ht : start+1+gs.length ≤ rows := by simp only [List.length_cons] at h; omega
    simp only [qmaGridCircuitFrom,List.mem_append,List.mem_singleton] at hk
    rcases hk with (hk | rfl) | hk
    · exact qmaGridTransfer_wellFormed rows width _ k hk
    · exact qmaMapGate_wellFormed width _ _ (qmaGridRow_injective rows width _)
        g (hg g (by simp))
    · exact ih (start+1) ht (fun k hk => hg k (by simp [hk])) k hk

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The lifted circuit starts with exactly the original witness and zero fresh wires. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

abbrev qmaPaddedCircuit (c : QMACircuit) (extra : ℕ) : QMACircuit :=
  ⟨c.work+extra,c.witness,
    c.gates.map (qmaMapGate c.work (c.work+extra) (qmaPaddedLeft c.work extra))⟩

theorem qmaPaddedCircuit_wellFormed (c : QMACircuit) (hc : c.WellFormed) (extra : ℕ) :
    (qmaPaddedCircuit c extra).WellFormed := by
  refine ⟨hc.1.trans (Nat.le_add_right _ _),?_⟩
  intro g hg
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hg
  exact qmaMapGate_wellFormed c.work (c.work+extra) _
    (qmaPaddedLeft_injective c.work extra) f (hc.2 f hf)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridAcceptance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete fresh-row circuit preserves verifier acceptance exactly. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

abbrev qmaGridCircuit (c : QMACircuit) : QMACircuit :=
  ⟨qmaGridWork c.gates.length c.work,c.witness,
    qmaGridCircuitFrom c.gates.length c.work 0 c.gates (by omega)⟩

theorem qmaGridCircuit_wellFormed (c : QMACircuit) (hc : c.WellFormed) :
    (qmaGridCircuit c).WellFormed := by
  refine ⟨?_,qmaGridCircuitFrom_wellFormed _ _ _ _ _ hc.2⟩
  exact hc.1.trans (Nat.le_add_right _ _)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRowInsertion
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem qmaMapGate_sites (sourceWork targetWork : ℕ)
    (f : Fin (sourceWork+1) → Fin (targetWork+1)) (g : QMAGate) :
    qmaGateSites targetWork (qmaMapGate sourceWork targetWork f g) =
      (qmaGateSites sourceWork g).image f := by
  cases g <;> simp [qmaMapGate,qmaGateSites,qmaQubit_fin]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRowStageSupport
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each sweep stage uses only vertical transfers and its single horizontal gate. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaWireSwap_sites {work : ℕ} (i j : Fin (work+1))
    (g : QMAGate) (hg : g ∈ qmaWireSwapGates i j) :
    ∀ k ∈ qmaGateSites work g, k = i ∨ k = j := by
  simp only [qmaWireSwapGates,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl <;>
    simp [qmaGateSites,qmaQubit_fin,or_comm]

theorem qmaAdjacentGate_window (work : ℕ) (g : QMAGate)
    (hg : g.WellFormed (work+1)) (ha : g.Adjacent) :
    ∃ lo : Fin (work+1), ∀ i ∈ qmaGateSites work g,
      lo.val ≤ i.val ∧ i.val ≤ lo.val+1 := by
  cases g with
  | hadamard i =>
    refine ⟨⟨i,hg⟩,?_⟩
    intro k hk
    simp only [qmaGateSites,Finset.mem_singleton] at hk
    subst k
    simp [qmaQubit,Nat.mod_eq_of_lt hg]
  | phaseT i =>
    refine ⟨⟨i,hg⟩,?_⟩
    intro k hk
    simp only [qmaGateSites,Finset.mem_singleton] at hk
    subst k
    simp [qmaQubit,Nat.mod_eq_of_lt hg]
  | controlledNot i j =>
    refine ⟨⟨min i j,lt_of_le_of_lt (min_le_left _ _) hg.1⟩,?_⟩
    intro k hk
    simp only [qmaGateSites,Finset.mem_insert,Finset.mem_singleton] at hk
    change i+1 = j ∨ j+1 = i at ha
    rcases hk with rfl | rfl
    · simp only [qmaQubit,Fin.val_mk,Nat.mod_eq_of_lt hg.1]
      omega
    · simp only [qmaQubit,Fin.val_mk,Nat.mod_eq_of_lt hg.2.1]
      omega

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete distributed reference Hamiltonian and its exact sector matrices. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

def qmaReferenceFamily (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ) (Δ : ℝ) :
    Matrix (SourceSpinBasis (n+1) × α) (SourceSpinBasis (n+1) × α) ℂ :=
  (∑ i, qmaDistributedRebitTerm (n+1) i (A i))+
    (Δ:ℂ) • (qmaReferenceYPenalty n ⊗ₖ (1 : Matrix α α ℂ))

def qmaReferenceSector (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ)
    (Δ : ℝ) (s : SourceSpinBasis (n+1)) : Matrix α α ℂ :=
  (∑ i, qmaReferenceSectorTerm (n+1) i (A i) s)+
    ((Δ:ℂ)*(qmaReferenceWalls n s:ℂ)) • 1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space variational comparison for the actual distributed reference family. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

def qmaReferenceTrial (n : ℕ) (u : α → ℂ) : SourceSpinBasis (n+1) × α → ℂ :=
  (qmaReferenceExtension (α := α) (n+1)).mulVec
    (fun p => if p.1 = (fun _ => 1) then u p.2 else 0)

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

def qmaReferenceOnQubits (n : ℕ)
    (A : Fin (n+1) → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :=
  (qmaReferenceFamily n A 1).submatrix
    (Equiv.sumArrowEquivProdArrow (Fin (n+1)) ι (Fin 2))
    (Equiv.sumArrowEquivProdArrow (Fin (n+1)) ι (Fin 2))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateArrival
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The insertion column is an actual operand, so adjacent gates remain close to the sweep. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaGateSites_nonempty (work : ℕ) (g : QMAGate) : (qmaGateSites work g).Nonempty := by
  cases g <;> simp [qmaGateSites]

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

theorem qmaColumnTransfer_located (rows width : ℕ) (r : Fin rows)
    (cols : List (Fin (width+1))) (g : QMAGate) (j : Fin (width+1))
    (h : (g,j) ∈ qmaColumnTransfer (qmaGridQubit rows width r.castSucc)
      (qmaGridQubit rows width r.succ) cols) :
    QMALocatedGate rows width r.castSucc j g := by
  obtain ⟨_,hg⟩ := qmaColumnTransfer_member _ _ _ _ _ h
  intro k hk
  rcases qmaWireSwap_sites _ _ g hg k hk with rfl | rfl
  · exact ⟨r.castSucc,j,rfl,le_rfl,by simp,by omega,by omega⟩
  · exact ⟨r.succ,j,rfl,by simp,by simp,by omega,by omega⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reordering actual history terms preserves the full-space reference gap. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaOrderedReferenceHistory (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    Matrix (QMAHistoryReferenceBasis c) (QMAHistoryReferenceBasis c) ℂ :=
  qmaReferenceFamily (qmaHistoryReferenceWork c) (qmaOrderedReferenceTerms c hT τ) 1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCircuitPadding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem qmaNonemptyCircuit_wellFormed (c : QMACircuit) (hc : c.WellFormed) :
    (qmaNonemptyCircuit c).WellFormed := by
  refine ⟨hc.1,?_⟩
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hc.2 g hg
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl <;> exact Nat.succ_pos _

theorem qmaNonemptyCircuit_nearest (c : QMACircuit) :
    (qmaNearestCircuit (qmaNonemptyCircuit c)).gates ≠ [] := by
  simp [qmaNonemptyCircuit,List.flatMap_append,qmaNearestGate]

end ContinuumCoulomb

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

theorem touches_spec (c : QMACircuit) (i : Fin (c.work+1)) (g : QMAGate) :
    touches (c.work,i.val,g)=decide (i ∈ qmaGateSites c.work g) := by
  apply Bool.eq_iff_iff.mpr
  have ht (x : TouchInput) : touches x = true ↔
      gateLeft x.2.2 % (x.1+1)=x.2.1 ∨ gateRight x.2.2 % (x.1+1)=x.2.1 := by
    unfold touches
    rw [Bool.or_eq_true,decide_eq_true_eq,decide_eq_true_eq]
  rw [ht,decide_eq_true_eq]
  cases g <;>
    simp only [gateLeft,gateRight,qmaGateSites,Finset.mem_singleton,
      Finset.mem_insert,Fin.ext_iff,qmaQubit] <;>
    omega

noncomputable def firstProgram :
    Procedure (listCode Procedure.boolCode) unaryCode first :=
  (foldProgram.comp ((Procedure.listReverse Procedure.boolCode false).pair
    (Procedure.constant _ unaryCode 0))).congrFun (by
      intro xs
      simp only [Function.comp_apply,List.foldl_reverse,first])

noncomputable def touchListProgram : Procedure inputCode
    (listCode Procedure.boolCode) touchList := by
  let circuit := Procedure.first circuitCode Nat.bits
  let site := Procedure.second circuitCode Nat.bits
  let work := Procedure.unaryToBits.comp (workProgram.comp circuit)
  let env := work.pair site
  let test : Procedure (prodCode (prodCode Nat.bits Nat.bits) gateCode)
      Procedure.boolCode (fun x => touches (x.1.1,x.1.2,x.2)) := by
    let context := Procedure.first (prodCode Nat.bits Nat.bits) gateCode
    exact touchesProgram.comp
      (((Procedure.first Nat.bits Nat.bits).comp context).pair
        (((Procedure.second Nat.bits Nat.bits).comp context).pair
          (Procedure.second (prodCode Nat.bits Nat.bits) gateCode)))
  exact (Procedure.listMapWith (f := fun e g => touches (e.1,e.2,g))
    (.hadamard 0) false test).comp (env.pair (gatesProgram.comp circuit))

noncomputable def program : Procedure inputCode unaryCode value :=
  firstProgram.comp touchListProgram

end ContinuumCoulomb.QuantumFirstUseProgram

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

noncomputable opaque baseLeftProgram : Procedure inputCode Nat.bits (fun x => 4*x.2.2.1.1) :=
  Procedure.binaryMul.comp ((Procedure.constant inputCode Nat.bits 4).pair leftProgram)
noncomputable opaque baseRightProgram : Procedure inputCode Nat.bits (fun x => 4*x.2.2.1.2) :=
  Procedure.binaryMul.comp ((Procedure.constant inputCode Nat.bits 4).pair rightProgram)

noncomputable opaque shiftedLeftProgram (p : ℕ) : Procedure inputCode Nat.bits (fun x => 4*x.2.2.1.1+p) :=
  Procedure.binaryAdd.comp (baseLeftProgram.pair (Procedure.constant inputCode Nat.bits p))
noncomputable opaque shiftedRightProgram (p : ℕ) : Procedure inputCode Nat.bits (fun x => 4*x.2.2.1.2+p) :=
  Procedure.binaryAdd.comp (baseRightProgram.pair (Procedure.constant inputCode Nat.bits p))

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

noncomputable opaque penaltyBaseProgram : Procedure penaltyCode Nat.bits (fun x => 4*x.1) :=
  Procedure.binaryMul.comp ((Procedure.constant penaltyCode Nat.bits 4).pair penaltyIndexProgram)
noncomputable opaque penaltyShiftProgram (i : ℕ) : Procedure penaltyCode Nat.bits (fun x => 4*x.1+i) :=
  Procedure.binaryAdd.comp (penaltyBaseProgram.pair (Procedure.constant penaltyCode Nat.bits i))
noncomputable opaque penaltySquareProgram : Procedure penaltyCode ratCode (fun x => x.2^2) :=
  (Procedure.ratMul.comp (penaltyScaleProgram.pair penaltyScaleProgram)).congrFun
    (by intro x; change x.2*x.2 = x.2^2; ring)
noncomputable opaque penaltyBondProgram (e : Fin 6) : Procedure penaltyCode bondCode
    (fun x => (4*x.1+(qmaFourEdgeLeft e).val,4*x.1+(qmaFourEdgeRight e).val,x.2^2)) :=
  (penaltyShiftProgram _).pair ((penaltyShiftProgram _).pair penaltySquareProgram)
noncomputable opaque fullSixCountProgram : Procedure fullCode ratCode (fun x => (x.1:ℚ)*6) :=
  Procedure.ratMul.comp (fullCountRatProgram.pair (Procedure.constant fullCode ratCode 6))
noncomputable opaque fullPenaltyScalarProgram : Procedure fullCode ratCode (fun x => x.2.1.2^2*(x.1*6)) :=
  Procedure.ratMul.comp ((penaltySquareProgram.comp fullPenaltyInputProgram).pair fullSixCountProgram)

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathsGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit ordinary-spin edges for simultaneous path subdivisions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Kronecker Classical
variable {ν : Type*} [Fintype ν]

def qmaPathsGraph {n r : ℕ} (left right : ν → Fin n) (weight : ν → ℝ)
    (constant R : ℝ) (site : Fin r → Fin 2 → Fin n) (even : Fin r → Bool) (J : Fin r → ℝ) :
    Matrix (SourceSpinBasis (n+r*2)) (SourceSpinBasis (n+r*2)) ℂ :=
  qmaExchangeMatrix
    (qmaParallelGraphLeft left site)
    (qmaParallelGraphRight right (fun e => qmaPathMember (even e)))
    (qmaParallelGraphWeight weight (R^2) (fun e => qmaPathAmplitude (even e) R (J e)))
    ((constant+∑ e, qmaPathOffset (J e))+3*r*(R^2))

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
open Matrix MediatorGraph
open scoped BigOperators Kronecker Classical
variable {ν : Type*} [Fintype ν]

def qmaCrossingsGraph {n r : ℕ} (left right : ν → Fin n) (weight : ν → ℝ)
    (constant R : ℝ) (site : Fin r → Fin 4 → Fin n) (J K : Fin r → ℝ) :
    Matrix (SourceSpinBasis (n+r*2)) (SourceSpinBasis (n+r*2)) ℂ :=
  qmaExchangeMatrix
    (qmaParallelGraphLeft (qmaCrossingsBaseLeft left site) site)
    (qmaParallelGraphRight (qmaCrossingsBaseRight right site) (fun _ => qmaCrossingMember))
    (qmaParallelGraphWeight (qmaCrossingsBaseWeight weight J K) (R^2)
      (fun e => qmaCrossingAmplitude R (J e) (K e)))
    ((constant+∑ e, qmaCrossingOffset (J e) (K e))+3*r*(R^2))

end ContinuumCoulomb

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

noncomputable def neighborIndexProgram :
    Procedure (prodCode pairCode pairCode) Nat.bits
      (fun x => (qmaGridNeighborIndex x.1 x.2).val) := by
  let p := Procedure.first pairCode pairCode
  let q := Procedure.second pairCode pairCode
  let px := (Procedure.first Nat.bits Nat.bits).comp p
  let py := (Procedure.second Nat.bits Nat.bits).comp p
  let qx := (Procedure.first Nat.bits Nat.bits).comp q
  let qy := (Procedure.second Nat.bits Nat.bits).comp q
  let plus (v : Procedure (prodCode pairCode pairCode) Nat.bits (fun x => x.1.1)) :=
    Procedure.binaryAdd.comp (v.pair (Procedure.constant _ Nat.bits 1))
  let px1 := plus px
  let py1 := Procedure.binaryAdd.comp (py.pair (Procedure.constant _ Nat.bits 1))
  let qx1 := Procedure.binaryAdd.comp (qx.pair (Procedure.constant _ Nat.bits 1))
  exact (Procedure.conditional (Procedure.binaryEq.comp (qx.pair px1))
    (Procedure.constant _ Nat.bits 0)
    (Procedure.conditional (Procedure.binaryEq.comp (qy.pair py1))
      (Procedure.constant _ Nat.bits 1)
      (Procedure.conditional (Procedure.binaryEq.comp (qx1.pair px))
        (Procedure.constant _ Nat.bits 2) (Procedure.constant _ Nat.bits 3)))).congrFun (by
          intro x
          simp only [Function.comp_apply,qmaGridNeighborIndex,decide_eq_true_eq]
          split_ifs <;> rfl)

noncomputable def visitProgram : Procedure inputCode visitCode (fun x => visit x.2 x.1) := by
  let i := Procedure.unaryToBits.comp (Procedure.first unaryCode (listCode pairCode))
  let xs := Procedure.second unaryCode (listCode pairCode)
  let get (j : ℕ) := (Procedure.listGet pairCode (0,0)).comp
    ((Procedure.binaryAdd.comp (i.pair (Procedure.constant inputCode Nat.bits j))).pair xs)
  let center := get 1
  let left := neighborIndexProgram.comp (center.pair (get 0))
  let right := neighborIndexProgram.comp (center.pair (get 2))
  exact (center.pair (left.pair right)).congrFun (by
    intro x
    simp only [Function.comp_apply,id_eq,Nat.add_zero,visit,lookup])

noncomputable def bothProgram : Procedure visitCode (listCode visitCode) both := by
  let v := Procedure.identity visitCode
  let rev := (Procedure.first pairCode pairCode).pair
    ((Procedure.swap Nat.bits Nat.bits).comp (Procedure.second pairCode pairCode))
  exact (Procedure.listCons visitCode).comp (v.pair
    ((Procedure.listCons visitCode).comp
      (rev.pair (Procedure.constant visitCode (listCode visitCode) []))))

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

noncomputable def neighborProgram : Procedure Nat.bits Nat.bits qmaPortNeighborIndex := by
  let half := Procedure.binaryDiv.comp
    ((Procedure.identity Nat.bits).pair (Procedure.constant Nat.bits Nat.bits 2))
  let parity := Procedure.binaryMod.comp
    ((Procedure.identity Nat.bits).pair (Procedure.constant Nat.bits Nat.bits 2))
  let isOdd := Procedure.binaryEq.comp (parity.pair (Procedure.constant Nat.bits Nat.bits 1))
  let up := Procedure.binaryAdd.comp (half.pair (Procedure.constant Nat.bits Nat.bits 1))
  let down := Procedure.binarySub.comp (half.pair (Procedure.constant Nat.bits Nat.bits 1))
  exact (Procedure.conditional isOdd up down).congrFun (by
    intro k
    simp only [Function.comp_apply,id_eq,decide_eq_true_eq,qmaPortNeighborIndex])

end ContinuumCoulomb.QuantumPortChainProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListPathProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

def inputCode : Input → List Bool :=
  prodCode parametersCode (prodCode unaryCode bondCode)

noncomputable opaque countProgram : Procedure inputCode Nat.bits (fun x => x.1.1) :=
  Procedure.unaryToBits.comp ((Procedure.first unaryCode
    (prodCode Procedure.boolCode ratCode)).comp (Procedure.first _ _))
noncomputable opaque indexProgram : Procedure inputCode Nat.bits (fun x => x.2.1) :=
  Procedure.unaryToBits.comp ((Procedure.first unaryCode bondCode).comp (Procedure.second _ _))
noncomputable opaque sourceProgram : Procedure inputCode bondCode (fun x => x.2.2) :=
  (Procedure.second unaryCode bondCode).comp (Procedure.second _ _)
noncomputable opaque baseProgram : Procedure inputCode Nat.bits (fun x => x.1.1+2*x.2.1) :=
  Procedure.binaryAdd.comp (countProgram.pair
    (Procedure.binaryMul.comp ((Procedure.constant inputCode Nat.bits 2).pair indexProgram)))
noncomputable opaque nextProgram : Procedure inputCode Nat.bits (fun x => x.1.1+2*x.2.1+1) :=
  Procedure.binaryAdd.comp (baseProgram.pair (Procedure.constant inputCode Nat.bits 1))
noncomputable opaque parityProgram : Procedure inputCode Procedure.boolCode (fun x => x.1.2.1) :=
  (Procedure.first Procedure.boolCode ratCode).comp
    ((Procedure.second unaryCode (prodCode Procedure.boolCode ratCode)).comp (Procedure.first _ _))

noncomputable opaque leftProgram (k : Fin 3) : Procedure inputCode Nat.bits (fun x => left x k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact baseProgram
  refine Fin.cases ?_ (fun k => ?_) k
  · exact (Procedure.first Nat.bits (prodCode Nat.bits ratCode)).comp sourceProgram
  refine Fin.cases ?_ (fun k => Fin.elim0 k) k
  exact (Procedure.first Nat.bits ratCode).comp
    ((Procedure.second Nat.bits (prodCode Nat.bits ratCode)).comp sourceProgram)

noncomputable opaque rightProgram (k : Fin 3) : Procedure inputCode Nat.bits (fun x => right x k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact nextProgram
  refine Fin.cases ?_ (fun k => ?_) k
  · exact baseProgram
  refine Fin.cases ?_ (fun k => Fin.elim0 k) k
  exact (Procedure.conditional parityProgram baseProgram nextProgram).congrFun (by
    intro x
    cases h : x.1.2.1 <;> simp [right,h])

def familyCode : FamilyInput → List Bool := prodCode parametersCode (listCode bondCode)

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

def inputCode : Input → List Bool :=
  prodCode headCode (prodCode (listCode bondCode) (listCode bondCode))

noncomputable opaque headProgram : Procedure inputCode headCode Prod.fst := Procedure.first _ _
noncomputable opaque countInputProgram : Procedure inputCode unaryCode (fun x => x.1.1) :=
  (Procedure.first _ _).comp headProgram
noncomputable opaque parityProgram : Procedure inputCode Procedure.boolCode (fun x => x.1.2.1) :=
  (Procedure.first _ _).comp ((Procedure.second _ _).comp headProgram)
noncomputable opaque constantsProgram : Procedure inputCode (prodCode ratCode ratCode)
    (fun x => x.1.2.2) :=
  (Procedure.second _ _).comp ((Procedure.second _ _).comp headProgram)
noncomputable opaque listsProgram :
    Procedure inputCode (prodCode (listCode bondCode) (listCode bondCode)) Prod.snd := Procedure.second _ _
noncomputable opaque retainedProgram : Procedure inputCode (listCode bondCode) (fun x => x.2.1) :=
  (Procedure.first _ _).comp listsProgram
noncomputable opaque selectedProgram : Procedure inputCode (listCode bondCode) (fun x => x.2.2) :=
  (Procedure.second _ _).comp listsProgram
noncomputable opaque countProgram : Procedure inputCode unaryCode count := by
  let n := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode zeroBond).comp selectedProgram
  exact Procedure.unaryAdd.comp (countInputProgram.pair
    (Procedure.unaryMul.comp (n.pair (Procedure.constant inputCode unaryCode 2))))

end ContinuumCoulomb.QuantumListPathStep

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSiteRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The terminal scan is independent of the finite vertex enumeration.
It returns the actual terminal in the emitted position tape. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSiteProgram
open QuantumRouteCode QuantumCrossingListBlock
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) {n : ℕ}
    (σ : Fin n ≃ Fin (P.finishedGraph N D).n) (pos : Fin n → Pair)
    (hpos : ∀ v, P.finishedPosition N D (σ v)=pos v)

theorem relabeled_sites_global : Function.Injective
    (fun t : Fin P.crossingCells.card × Fin 4 => σ.symm (P.crossingSiteFin N hD t.1 t.2)) := by
  intro x y h
  exact P.crossingSiteFin_global N hD (σ.symm.injective h)

theorem reordered_sites_global {r : ℕ} (τ : Fin r ≃ Fin P.crossingCells.card) :
    Function.Injective
      (fun t : Fin r × Fin 4 => σ.symm (P.crossingSiteFin N hD (τ t.1) t.2)) := by
  exact (relabeled_sites_global P N hD σ).comp
    (Equiv.prodCongr τ (Equiv.refl (Fin 4))).injective

end ContinuumCoulomb.QuantumCrossingSiteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySiteProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal ordered gate and propagation support lists. The values agree
with the exact support order used by the local history matrix tables. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySiteProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

noncomputable def gateLabelsProgram :
    Procedure gateInputCode (listCode Nat.bits) gateLabels := by
  let work := Procedure.first Nat.bits gateCode
  let gate := Procedure.second Nat.bits gateCode
  let modulus := Procedure.successor.comp work
  let left := Procedure.binaryMod.comp ((gateLeftProgram.comp gate).pair modulus)
  let right := Procedure.binaryMod.comp ((gateRightProgram.comp gate).pair modulus)
  let nil := Procedure.constant gateInputCode (listCode Nat.bits) []
  let single := (Procedure.listCons Nat.bits).comp (left.pair nil)
  let pair := (Procedure.listCons Nat.bits).comp
    (left.pair ((Procedure.listCons Nat.bits).comp (right.pair nil)))
  let isCnot := Procedure.binaryEq.comp ((gateTagProgram.comp gate).pair
    (Procedure.constant gateInputCode Nat.bits 2))
  exact (Procedure.conditional isCnot pair single).congrFun (by
    intro x
    simp only [Function.comp_apply,gateLabels,decide_eq_true_eq])

noncomputable def gateAtProgram : Procedure inputCode gateCode gateAt := by
  let circuit := Procedure.first circuitCode Nat.bits
  let index := Procedure.second circuitCode Nat.bits
  exact ((Procedure.listGet gateCode (.hadamard 0)).comp
    (index.pair (gatesProgram.comp circuit))).congrFun (by
      intro x
      simp only [Function.comp_apply,gateAt,List.headD_eq_head?_getD,
        List.head?_drop,List.getD_eq_getElem?_getD])

noncomputable def propagationLabelsProgram :
    Procedure inputCode (listCode Nat.bits) propagationLabels := by
  let circuit := Procedure.first circuitCode Nat.bits
  let index := Procedure.second circuitCode Nat.bits
  let work := Procedure.unaryToBits.comp (workProgram.comp circuit)
  let gates := gatesProgram.comp circuit
  let count := Procedure.unaryToBits.comp
    ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength gateCode (.hadamard 0)).comp gates)
  let offset := Procedure.binaryAdd.comp (count.pair (Procedure.constant inputCode Nat.bits 2))
  let nil := Procedure.constant inputCode (listCode Nat.bits) []
  let one := Procedure.successor.comp index
  let two := Procedure.successor.comp one
  let clock := (Procedure.listCons Nat.bits).comp
    (index.pair ((Procedure.listCons Nat.bits).comp
      (one.pair ((Procedure.listCons Nat.bits).comp (two.pair nil)))))
  let gateSites := gateLabelsProgram.comp (work.pair gateAtProgram)
  let translated := (Procedure.listMapWith (f := fun a b : ℕ => a+b) 0 0
    Procedure.binaryAdd).comp (offset.pair gateSites)
  exact (Procedure.listAppend Nat.bits 0).comp (clock.pair translated)

end ContinuumCoulomb.QuantumHistorySiteProgram

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

noncomputable opaque atIndexProgram : Procedure indexCode descriptorCode
    (fun x => atIndex x.1 x.2.1 x.2.2) := by
  let work := Procedure.first Nat.bits (prodCode Nat.bits Nat.bits)
  let rest := Procedure.second Nat.bits (prodCode Nat.bits Nat.bits)
  let time := (Procedure.first Nat.bits Nat.bits).comp rest
  let index := (Procedure.second Nat.bits Nat.bits).comp rest
  let one := Procedure.successor.comp time
  let three := Procedure.binaryAdd.comp
    (one.pair (Procedure.constant indexCode Nat.bits 2))
  let inputs := Procedure.binaryAdd.comp (three.pair (Procedure.successor.comp work))
  let afterInput := Procedure.successor.comp inputs
  let tag (n : ℕ) := Procedure.constant indexCode Nat.bits n
  let sub {f : IndexInput → ℕ} (bound : Procedure indexCode Nat.bits f) :
      Procedure indexCode Nat.bits (fun x => x.2.2-f x) :=
    Procedure.binarySub.comp (index.pair bound)
  let lt {f : IndexInput → ℕ} (bound : Procedure indexCode Nat.bits f) :
      Procedure indexCode Procedure.boolCode (fun x => decide (x.2.2<f x)) :=
    Procedure.binaryLt.comp (index.pair bound)
  exact (Procedure.conditional (lt one) ((tag 0).pair index)
    (Procedure.conditional (lt three) ((tag 1).pair (sub one))
    (Procedure.conditional (lt inputs) ((tag 2).pair (sub three))
    (Procedure.conditional (lt afterInput) ((tag 3).pair (tag 0))
      ((tag 4).pair (sub afterInput)))))).congrFun (by
        intro x
        simp only [atIndex,Function.comp_apply,decide_eq_true_eq])

noncomputable opaque sourceEntryProgram :
    Procedure (prodCode unaryCode circuitCode) descriptorCode
      (fun x => atIndex x.2.work x.2.gates.length x.1) := by
  let circuit := Procedure.second unaryCode circuitCode
  let index := Procedure.unaryToBits.comp (Procedure.first unaryCode circuitCode)
  let work := Procedure.unaryToBits.comp (workProgram.comp circuit)
  let time := Procedure.unaryToBits.comp (timeProgram.comp circuit)
  exact atIndexProgram.comp (work.pair (time.pair index))

noncomputable opaque sourceProgram : Procedure circuitCode (listCode descriptorCode) source :=
  ((Procedure.tabulate (f := fun c i => atIndex c.work c.gates.length i)
    (0,0) sourceEntryProgram).comp
      (countProgram.pair (Procedure.identity circuitCode))).congrFun (by intro c; rfl)

end ContinuumCoulomb.QuantumHistoryDescriptors

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

noncomputable opaque entryProgram (k : ℕ) : Procedure inputCode letterCode (entry k) :=
  (Procedure.listGet letterCode (0,0)).comp
    ((Procedure.constant inputCode Nat.bits k).pair entriesProgram)
noncomputable opaque indexProgram (k : ℕ) : Procedure inputCode Nat.bits (fun x => (entry k x).1) :=
  (Procedure.first Nat.bits Nat.bits).comp (entryProgram k)
noncomputable opaque labelProgram (k : ℕ) : Procedure inputCode Nat.bits (fun x => (entry k x).2) :=
  (Procedure.second Nat.bits Nat.bits).comp (entryProgram k)
noncomputable opaque labelTest (k a : ℕ) : Procedure inputCode Procedure.boolCode
    (fun x => decide ((entry k x).2=a)) :=
  Procedure.binaryEq.comp ((labelProgram k).pair (Procedure.constant inputCode Nat.bits a))
noncomputable opaque sameIndexProgram : Procedure inputCode Procedure.boolCode
    (fun x => decide ((entry 0 x).1=(entry 1 x).1)) :=
  Procedure.binaryEq.comp ((indexProgram 0).pair (indexProgram 1))

noncomputable opaque nonzeroFieldProgram (k : ℕ) :
    Procedure inputCode QuantumRawExchange.rawCode (fun x =>
      ((false,true),(((entry k x).1,0),((decide ((entry k x).2=1),false),x.2)))) :=
  (Procedure.constant inputCode (prodCode Procedure.boolCode Procedure.boolCode) (false,true)).pair
    (((indexProgram k).pair (Procedure.constant inputCode Nat.bits 0)).pair
      (((labelTest k 1).pair (Procedure.constant inputCode Procedure.boolCode false)).pair
        weightProgram))

noncomputable opaque fieldProgram (k : ℕ) : Procedure inputCode QuantumRawExchange.rawCode
    (fun x => field (entry k x) x.2) :=
  (Procedure.conditional (labelTest k 0) scalarProgram (nonzeroFieldProgram k)).congrFun (by
    intro x
    simp only [field,decide_eq_true_eq])

noncomputable opaque pairProgram : Procedure inputCode QuantumRawExchange.rawCode
    (fun x => pair (entry 0 x) (entry 1 x) x.2) :=
  (Procedure.constant inputCode (prodCode Procedure.boolCode Procedure.boolCode) (true,false)).pair
    (((indexProgram 0).pair (indexProgram 1)).pair
      (((labelTest 0 1).pair (labelTest 1 1)).pair weightProgram))

noncomputable opaque program : Procedure inputCode QuantumRawExchange.rawCode value := by
  let p := Procedure.conditional (lengthTest 0) scalarProgram
    (Procedure.conditional (lengthTest 1) (fieldProgram 0)
      (Procedure.conditional sameIndexProgram (fieldProgram 0)
        (Procedure.conditional (labelTest 0 0) (fieldProgram 1)
          (Procedure.conditional (labelTest 1 0) (fieldProgram 0) pairProgram))))
  exact p.congrFun (by
    intro x
    simpa only [lookupValue,Function.comp_apply,decide_eq_true_eq] using lookupValue_eq x)

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

noncomputable def takeProgram (d : ℕ) : Procedure labelsCode labelsCode
    (fun xs => xs.take d) := by
  induction d with
  | zero => exact (Procedure.constant labelsCode labelsCode []).congrFun (by intro xs; rfl)
  | succ d ih =>
    let cons := (Procedure.listCons labelCode).comp
      ((Procedure.listHead labelCode (0,0)).pair (ih.comp (Procedure.listTail labelCode)))
    exact (Procedure.conditional (Procedure.listEmpty labelCode)
      (Procedure.constant labelsCode labelsCode []) cons).congrFun (by
        intro xs
        cases xs <;> rfl)

noncomputable def dropProgram (d : ℕ) : Procedure labelsCode labelsCode
    (fun xs => xs.drop d) :=
  (Procedure.listDrop labelCode).comp
    ((Procedure.constant labelsCode Nat.bits d).pair (Procedure.identity labelsCode))

noncomputable opaque oddProgram : Procedure labelsCode Procedure.boolCode
    (fun xs => decide (Odd (yCount xs))) := by
  let head := Procedure.first labelCode Procedure.boolCode
  let letter := (Procedure.second Nat.bits Nat.bits).comp head
  let test := Procedure.binaryEq.comp
    (letter.pair (Procedure.constant (prodCode labelCode Procedure.boolCode) Nat.bits 2))
  let state := Procedure.second labelCode Procedure.boolCode
  let step := Procedure.boolXor.comp (test.pair state)
  let fold := Procedure.foldList (0,0) step (Polynomial.C 1) (by
    intro xs b i
    simp only [Procedure.boolCode,List.length_singleton,Polynomial.eval_C]
    exact le_rfl)
  exact (fold.comp ((Procedure.identity labelsCode).pair
    (Procedure.constant labelsCode Procedure.boolCode false))).congrFun (by
      intro xs
      simp only [Function.comp_apply,id_eq,fold_oddLetters,Bool.xor_false,oddLetters_eq])

noncomputable opaque axisProgram : Procedure labelsCode Nat.bits axis :=
  (Procedure.conditional oddProgram (Procedure.constant labelsCode Nat.bits 2)
    (Procedure.constant labelsCode Nat.bits 1)).congrFun (by
      intro xs
      simp only [axis,decide_eq_true_eq])

noncomputable opaque prefixProgram (d : ℕ) : Procedure blockCode labelsCode
    (fun x => x.2.take d) := (takeProgram d).comp labelsProgram
noncomputable opaque suffixProgram (d : ℕ) : Procedure blockCode labelsCode
    (fun x => x.2.drop d) := (dropProgram d).comp labelsProgram
noncomputable opaque mediatorLabelProgram (d : ℕ) : Procedure blockCode labelCode
    (fun x => (x.1,axis (x.2.take d))) :=
  mediatorProgram.pair (axisProgram.comp (prefixProgram d))
noncomputable def singletonProgram {α : Type} {ea : α → List Bool}
    (f : α → Letter) (p : Procedure ea labelCode f) :
    Procedure ea labelsCode (fun x => [f x]) :=
  (Procedure.listCons labelCode).comp (p.pair (Procedure.constant ea labelsCode []))

noncomputable opaque subdivisionProgram (d : ℕ) (k : Fin 4) :
    Procedure blockCode labelsCode (fun x => subdivision x.1 d x.2 k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact Procedure.constant blockCode labelsCode []
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact singletonProgram (fun x : BlockInput => (x.1,3))
        (mediatorProgram.pair (Procedure.constant blockCode Nat.bits 3))
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact (Procedure.listAppend labelCode (0,0)).comp
          ((prefixProgram d).pair (singletonProgram _ (mediatorLabelProgram d)))
      · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
        exact (Procedure.listAppend labelCode (0,0)).comp
          ((suffixProgram d).pair (singletonProgram _ (mediatorLabelProgram d)))

end ContinuumCoulomb.QuantumOrderedLabelData

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

noncomputable opaque couplingHalf : Procedure pairCode ratCode (fun x => x.2/2) :=
  Procedure.ratDiv.comp (coupling.pair (Procedure.constant pairCode ratCode 2))

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

noncomputable opaque weightsProgram : Procedure inputCode QuantumOrderedWeightProgram.inputCode weights :=
  precisionProgram.pair ((Procedure.listMap ([],0) 0
    (Procedure.second labelsCode ratCode)).comp entriesProgram)

end ContinuumCoulomb.QuantumOrderedLabelFamily

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

noncomputable opaque timeValueProgram : Procedure timeCode Nat.bits
    (fun x => timeValue x.1 x.2) := by
  let c := Procedure.first circuitCode descriptorCode
  let d := Procedure.second circuitCode descriptorCode
  let tag := (Procedure.first Nat.bits Nat.bits).comp d
  let index := (Procedure.second Nat.bits Nat.bits).comp d
  let time := Procedure.unaryToBits.comp (timeProgram.comp c)
  let last := Procedure.binarySub.comp
    (time.pair (Procedure.constant timeCode Nat.bits 1))
  let test (n : ℕ) := Procedure.binaryEq.comp
    (tag.pair (Procedure.constant timeCode Nat.bits n))
  let minWithLast {f : TimeInput → ℕ} (p : Procedure timeCode Nat.bits f) :
      Procedure timeCode Nat.bits (fun x => min (f x) (x.1.gates.length-1)) :=
    (Procedure.conditional (Procedure.binaryLe.comp (p.pair last)) p last).congrFun
      (by intro x; simp only [Function.comp_apply,id_eq,decide_eq_true_eq]; split_ifs <;> omega)
  let firstUse := Procedure.unaryToBits.comp
    (QuantumFirstUseProgram.program.comp (c.pair index))
  let boundary := Procedure.conditional
    (Procedure.binaryEq.comp (index.pair (Procedure.constant timeCode Nat.bits 0)))
    (Procedure.constant timeCode Nat.bits 0) last
  exact (Procedure.conditional (test 0) (minWithLast index)
    (Procedure.conditional (test 1) boundary
    (Procedure.conditional (test 2) (minWithLast firstUse)
    (Procedure.conditional (test 3) last index)))).congrFun (by
      intro x
      simp only [timeValue,Function.comp_apply,id_eq,decide_eq_true_eq])

noncomputable opaque chunkProgram : Procedure chunkCode (listCode descriptorCode) chunk := by
  let env := Procedure.first bucketCode descriptorCode
  let c := (Procedure.first circuitCode Nat.bits).comp env
  let t := (Procedure.second circuitCode Nat.bits).comp env
  let d := Procedure.second bucketCode descriptorCode
  let hit := Procedure.binaryEq.comp ((timeValueProgram.comp (c.pair d)).pair t)
  let nil := Procedure.constant chunkCode (listCode descriptorCode) []
  exact (Procedure.conditional hit ((Procedure.listCons descriptorCode).comp (d.pair nil))
    nil).congrFun (by intro x; simp only [chunk,Function.comp_apply,decide_eq_true_eq])

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

theorem fold_bound (xs ys : List ℕ) :
    (listCode Nat.bits (xs.foldl (fun zs a => insert a zs) ys)).length ≤
      (listCode Nat.bits xs).length+(listCode Nat.bits ys).length := by
  have h := QuantumWalkErasure.listCode_length_sublist Nat.bits (fold_sublist xs ys)
  have ha := listCode_length_append Nat.bits xs.reverse ys
  rw [listCode_length_rev] at ha
  omega

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

noncomputable def oneLabel {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea Nat.bits f) : Procedure ea (listCode Nat.bits) (fun x => [f x]) :=
  (Procedure.listCons Nat.bits).comp
    (p.pair (Procedure.constant ea (listCode Nat.bits) []))

noncomputable def consLabel {α : Type} {ea : α → List Bool}
    {f : α → ℕ} {g : α → List ℕ} (p : Procedure ea Nat.bits f)
    (q : Procedure ea (listCode Nat.bits) g) :
    Procedure ea (listCode Nat.bits) (fun x => f x::g x) :=
  (Procedure.listCons Nat.bits).comp (p.pair q)

noncomputable opaque distributedLabelsProgram : Procedure timeCode (listCode Nat.bits)
    (fun x => distributedLabels x.1 x.2) := by
  let c := Procedure.first circuitCode descriptorCode
  let d := Procedure.second circuitCode descriptorCode
  let tag := (Procedure.first Nat.bits Nat.bits).comp d
  let index := (Procedure.second Nat.bits Nat.bits).comp d
  let time := Procedure.unaryToBits.comp (timeProgram.comp c)
  let work := Procedure.unaryToBits.comp (workProgram.comp c)
  let const (n : ℕ) := Procedure.constant timeCode Nat.bits n
  let offset := Procedure.binaryAdd.comp (time.pair (const 2))
  let label := Procedure.binaryAdd.comp (offset.pair index)
  let fault := consLabel index (oneLabel (Procedure.successor.comp index))
  let boundary := Procedure.conditional
    (Procedure.binaryEq.comp (index.pair (const 0))) (oneLabel (const 0))
      (oneLabel (Procedure.successor.comp time))
  let firstUse := Procedure.unaryToBits.comp
    (QuantumFirstUseProgram.program.comp (c.pair index))
  let input := consLabel firstUse
    (consLabel (Procedure.successor.comp firstUse) (oneLabel label))
  let output := consLabel time (oneLabel (Procedure.binaryAdd.comp (offset.pair work)))
  let prop := QuantumHistorySiteProgram.propagationLabelsProgram.comp (c.pair index)
  let test (n : ℕ) := Procedure.binaryEq.comp (tag.pair (const n))
  exact (Procedure.conditional (test 0) fault (Procedure.conditional (test 1) boundary
    (Procedure.conditional (test 2) input (Procedure.conditional (test 3) output prop)))).congrFun
      (by intro x; simp only [distributedLabels,Function.comp_apply,id_eq,
        Nat.succ_eq_add_one,decide_eq_true_eq])

noncomputable opaque referenceWorkProgram : Procedure circuitCode Nat.bits referenceWork := by
  let time := Procedure.unaryToBits.comp timeProgram
  let work := Procedure.unaryToBits.comp workProgram
  let twice := Procedure.binaryMul.comp
    ((Procedure.constant circuitCode Nat.bits 2).pair time)
  exact Procedure.binaryAdd.comp
    ((Procedure.binaryAdd.comp (twice.pair work)).pair
      (Procedure.constant circuitCode Nat.bits 4))

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

def matrixCode : List Scalar → List Bool := listCode scalarCode

attribute [local instance] OAI.ContinuumCoulomb.QuantumFixedPauli.finDecision
noncomputable def entryProgram {β : Type} [Fintype β] (s t : β) :
    Procedure matrixCode scalarCode (fun xs => entry xs s t) :=
  (Procedure.listGet scalarCode (rat 0)).comp
    ((Procedure.constant matrixCode Nat.bits ((Fintype.equivFin (β×β)) (s,t)).val).pair
      (Procedure.identity matrixCode))

end ContinuumCoulomb.QuantumFixedPauli

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

noncomputable def matchesProgram :
    Procedure (prodCode Nat.bits (listCode Nat.bits)) (listCode Procedure.boolCode)
      (fun x => x.2.map (fun a => decide (a=x.1))) :=
  Procedure.listMapWith (f := fun label a => decide (a=label)) 0 false
    (Procedure.binaryEq.comp
      ((Procedure.second Nat.bits Nat.bits).pair (Procedure.first Nat.bits Nat.bits)))

noncomputable def indexProgram :
    Procedure (prodCode Nat.bits (listCode Nat.bits)) Nat.bits
      (fun x => x.2.idxOf x.1) :=
  ((Procedure.unaryToBits.comp QuantumFirstUseProgram.firstProgram).comp matchesProgram).congrFun
    (by
      intro x
      simp only [Function.comp_apply,id_eq]
      rw [QuantumFirstUseProgram.first_eq_findIdx,List.findIdx_map]
      change x.2.findIdx (fun a => decide (a=x.1)) = x.2.findIdx (fun a => a==x.1)
      congr 1)

noncomputable def program : Procedure inputCode Nat.bits value := by
  let label := Procedure.first Nat.bits (prodCode (listCode Nat.bits) (listCode Nat.bits))
  let rest := Procedure.second Nat.bits (prodCode (listCode Nat.bits) (listCode Nat.bits))
  let sites := (Procedure.first (listCode Nat.bits) (listCode Nat.bits)).comp rest
  let bits := (Procedure.second (listCode Nat.bits) (listCode Nat.bits)).comp rest
  exact (Procedure.listGet Nat.bits 0).comp
    ((indexProgram.comp (label.pair sites)).pair bits)

open QuantumOrderedSupport
open scoped Classical

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

noncomputable opaque rowProgram : Procedure queryCode Nat.bits (fun x => (row x.2 x.1).val) := by
  let q := Procedure.first Nat.bits dataCode
  let d := Procedure.second Nat.bits dataCode
  let labels := (Procedure.first (listCode Nat.bits)
    (prodCode (listCode Nat.bits) (listCode Nat.bits))).comp d
  let values := (Procedure.second (listCode Nat.bits)
    (prodCode (listCode Nat.bits) (listCode Nat.bits))).comp d
  let s := (Procedure.first (listCode Nat.bits) (listCode Nat.bits)).comp values
  exact Procedure.binaryMod.comp
    ((QuantumSupportLookup.program.comp (q.pair (labels.pair s))).pair
      (Procedure.constant queryCode Nat.bits 2))

noncomputable opaque columnProgram :
    Procedure queryCode Nat.bits (fun x => (column x.2 x.1).val) := by
  let q := Procedure.first Nat.bits dataCode
  let d := Procedure.second Nat.bits dataCode
  let labels := (Procedure.first (listCode Nat.bits)
    (prodCode (listCode Nat.bits) (listCode Nat.bits))).comp d
  let values := (Procedure.second (listCode Nat.bits)
    (prodCode (listCode Nat.bits) (listCode Nat.bits))).comp d
  let t := (Procedure.second (listCode Nat.bits) (listCode Nat.bits)).comp values
  exact Procedure.binaryMod.comp
    ((QuantumSupportLookup.program.comp (q.pair (labels.pair t))).pair
      (Procedure.constant queryCode Nat.bits 2))

noncomputable opaque readPairProgram :
    Procedure queryCode (prodCode Nat.bits Nat.bits) readPair :=
  rowProgram.pair columnProgram

noncomputable opaque matrixEntryProgram (A : Fin 2 → Fin 2 → Scalar) :
    Procedure (prodCode Nat.bits Nat.bits) scalarCode (matrixEntry A) := by
  let l := Procedure.first Nat.bits Nat.bits
  let r := Procedure.second Nat.bits Nat.bits
  let two := Procedure.constant (prodCode Nat.bits Nat.bits) Nat.bits 2
  let zero := Procedure.constant (prodCode Nat.bits Nat.bits) Nat.bits 0
  let bl := Procedure.binaryEq.comp ((Procedure.binaryMod.comp (l.pair two)).pair zero)
  let br := Procedure.binaryEq.comp ((Procedure.binaryMod.comp (r.pair two)).pair zero)
  exact ((Procedure.ofBool₂ scalarCode
    (fun b c => A (if b then 0 else 1) (if c then 0 else 1))).comp
      (bl.pair br)).congrFun (by
        intro x
        simp only [Function.comp_apply,decide_eq_true_eq,matrixEntry,bit_as_test])

end ContinuumCoulomb.QuantumHistoryBitProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDiagonalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar-register evaluation of the diagonal history descriptors. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar
open QuantumCircuitCode QuantumHistoryDescriptors QuantumHistoryBitProgram

noncomputable opaque clockBaseProgram : Procedure inputCode Nat.bits
    (fun x => referenceWork x.1+1) :=
  Procedure.successor.comp (referenceWorkProgram.comp circuitProgram)

noncomputable opaque workBaseProgram : Procedure inputCode Nat.bits
    (fun x => referenceWork x.1+1+(x.1.gates.length+2)) :=
  Procedure.binaryAdd.comp (clockBaseProgram.pair
    (Procedure.binaryAdd.comp (timeProgram.pair (Procedure.constant inputCode Nat.bits 2))))

noncomputable def clockValueProgram {f : Input → ℕ} (p : Procedure inputCode Nat.bits f) :
    Procedure inputCode Nat.bits (fun x => (clockRow x.1 x.2.2 (f x)).val) :=
  rowProgram.comp ((Procedure.binaryAdd.comp (clockBaseProgram.pair p)).pair dataProgram)

noncomputable def workValueProgram {f : Input → ℕ} (p : Procedure inputCode Nat.bits f) :
    Procedure inputCode Nat.bits (fun x => (workRow x.1 x.2.2 (f x)).val) :=
  rowProgram.comp ((Procedure.binaryAdd.comp (workBaseProgram.pair p)).pair dataProgram)

noncomputable opaque firstUseProgram : Procedure inputCode Nat.bits
    (fun x => QuantumFirstUseProgram.value (x.1,x.2.1.2)) :=
  Procedure.unaryToBits.comp
    (QuantumFirstUseProgram.program.comp (circuitProgram.pair indexProgram))

noncomputable opaque weightProgram : Procedure inputCode scalarCode
    (fun x => rat (weight x.1 x.2.1 x.2.2)) := by
  let const (n : ℕ) := Procedure.constant inputCode Nat.bits n
  let eq {f : Input → ℕ} (p : Procedure inputCode Nat.bits f) (n : ℕ) :=
    Procedure.binaryEq.comp (p.pair (const n))
  let both {f g : Input → Bool} (p : Procedure inputCode Procedure.boolCode f)
      (q : Procedure inputCode Procedure.boolCode g) := Procedure.boolAnd.comp (p.pair q)
  let not {f : Input → Bool} (p : Procedure inputCode Procedure.boolCode f) :=
    Procedure.boolNot.comp p
  let scalar (n : ℚ) := Procedure.constant inputCode scalarCode (rat n)
  let zero := scalar 0
  let one := scalar 1
  let fault := Procedure.conditional
    (both (eq (clockValueProgram indexProgram) 0)
      (eq (clockValueProgram (Procedure.successor.comp indexProgram)) 1)) one zero
  let left := Procedure.conditional (eq (clockValueProgram (const 0)) 1) zero one
  let right := Procedure.conditional
    (eq (clockValueProgram (Procedure.successor.comp timeProgram)) 0) zero one
  let boundary := Procedure.conditional (eq indexProgram 0) left right
  let witness := Procedure.unaryToBits.comp (witnessProgram.comp circuitProgram)
  let initial := both (eq (clockValueProgram firstUseProgram) 1)
    (both (eq (clockValueProgram (Procedure.successor.comp firstUseProgram)) 0)
      (both (Procedure.binaryLe.comp (witness.pair indexProgram))
        (not (eq (workValueProgram indexProgram) 0))))
  let input := Procedure.conditional initial (scalar 14) zero
  let work := Procedure.unaryToBits.comp (workProgram.comp circuitProgram)
  let output := Procedure.conditional
    (both (eq (clockValueProgram timeProgram) 1) (not (eq (workValueProgram work) 1))) one zero
  exact (Procedure.conditional (eq tagProgram 0) fault
    (Procedure.conditional (eq tagProgram 1) boundary
    (Procedure.conditional (eq tagProgram 2) input
    (Procedure.conditional (eq tagProgram 3) output zero)))).congrFun (by
      intro x
      simp only [weight,Function.comp_apply,id_eq,decide_eq_true_eq,Bool.and_eq_true,
        Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not,ne_eq,Fin.ext_iff,Fin.val_zero,
        Fin.val_one,Nat.succ_eq_add_one]
      simp only [apply_ite rat])

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

noncomputable def tableEntryProgram (n : ℕ) (s t : Fin n → Fin 2) :
    Procedure tableCode scalarCode (fun x => table n x s t) := by
  by_cases h : s=t
  · exact (weightProgram.comp (tableEntryInputProgram n s t)).congrFun
      (by intro x; simp only [table,h,ite_true, if_true,Function.comp_apply])
  · exact (Procedure.constant tableCode scalarCode (rat 0)).congrFun
      (by intro x; simp only [table,h,ite_false, if_false])

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

theorem fold_bound (xs ys : List Pair) :
    (listCode pairCode (xs.foldl (fun zs a => insertPair a zs) ys)).length ≤
      (listCode pairCode xs).length+(listCode pairCode ys).length := by
  have h := QuantumWalkErasure.listCode_length_sublist pairCode (fold_sublist xs ys)
  have ha := listCode_length_append pairCode xs.reverse ys
  rw [listCode_length_rev] at ha
  omega

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

def inputVisits (x : Input) : List Visit := (x.2.map visits).flatten

def beforeCrossings (x : Input) : Table := (x.1,inputVisits x,[])

def compile (x : Input) : Table := computedTable (beforeCrossings x)

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

def value (x : QuantumPathTable.Input) : List Pair :=
  (QuantumPathTable.compile x).2.2.dedup

theorem nodup (x : QuantumPathTable.Input) : (value x).Nodup := List.nodup_dedup _

end ContinuumCoulomb.QuantumDistinctCrossings

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
open Matrix MediatorGraph
open scoped BigOperators Kronecker Classical
variable {ν : Type*} [Fintype ν]

def qmaForksGraph {n r : ℕ} (left right : ν → Fin n) (weight : ν → ℝ)
    (constant R : ℝ) (site : Fin r → Fin 3 → Fin n) (J K : Fin r → ℝ) :
    Matrix (SourceSpinBasis (n+r*2)) (SourceSpinBasis (n+r*2)) ℂ :=
  qmaExchangeMatrix
    (qmaParallelGraphLeft (qmaForksBaseLeft left site) site)
    (qmaParallelGraphRight (qmaForksBaseRight right site) (fun _ => qmaForkMember))
    (qmaParallelGraphWeight (qmaForksBaseWeight weight J K) (R^2)
      (fun e => qmaForkAmplitude R (J e) (K e)))
    ((constant+∑ e, qmaForkOffset (J e) (K e))+3*r*(R^2))

end ContinuumCoulomb

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

noncomputable opaque sixCountProgram : Procedure scheduleCode ratCode (fun x => 6*(x.1:ℚ)) :=
  Procedure.ratMul.comp ((Procedure.constant scheduleCode ratCode 6).pair countRatProgram)
noncomputable opaque termCountProgram : Procedure scheduleCode ratCode (fun x => 25*(x.2.2.length:ℚ)) :=
  Procedure.ratMul.comp ((Procedure.constant scheduleCode ratCode 25).pair scheduleLengthRatProgram)
noncomputable opaque edgeCountProgram : Procedure scheduleCode ratCode
    (fun x => 6*(x.1:ℚ)+25*(x.2.2.length:ℚ)) :=
  Procedure.ratAdd.comp (sixCountProgram.pair termCountProgram)

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListBackground
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained part of a literal fork state has exactly the coefficient
budget and finite exchange matrix used by the parallel-fork estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram QuantumRawExchange
open scoped BigOperators Classical

def backgroundGraph (s : State) (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) : QMARationalExchangeGraph :=
  QuantumListGraph.ofBonds s.1 (background s) s.2.2.1 hb hn

end ContinuumCoulomb.QuantumForkList

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

def stateCode : State → List Bool :=
  prodCode unaryCode (prodCode (listCode MediatorListProgram.bondCode)
    (prodCode ratCode groupsCode))

noncomputable def portAtProgram :
    Procedure (prodCode unaryCode (listCode portCode)) portCode
      (fun x => portAt x.2 x.1) :=
  (Procedure.listGet portCode (0,0)).comp
    ((Procedure.unaryToBits.comp (Procedure.first unaryCode (listCode portCode))).pair
      (Procedure.second unaryCode (listCode portCode)))

noncomputable def pairAtProgram :
    Procedure (prodCode unaryCode (listCode portCode)) pairCode
      (fun x => (portAt x.2 (2*x.1),portAt x.2 (2*x.1+1))) := by
  let i := Procedure.first unaryCode (listCode portCode)
  let xs := Procedure.second unaryCode (listCode portCode)
  let twice := (Procedure.unaryAdd.comp (i.pair i)).congrFun (by intro x; change x.1+x.1=2*x.1; omega)
  exact (portAtProgram.comp (twice.pair xs)).pair
    (portAtProgram.comp ((Procedure.unarySuccessor.comp twice).pair xs))

noncomputable def pairsProgram : Procedure (listCode portCode) (listCode pairCode) pairs := by
  let count := halfProgram.comp (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength portCode (0,0))
  exact (Procedure.tabulate (f := fun ps i => (portAt ps (2*i),portAt ps (2*i+1)))
    ((0,0),(0,0)) pairAtProgram).comp (count.pair (Procedure.identity (listCode portCode)))

noncomputable def unpairedProgram : Procedure (listCode portCode) (listCode portCode) unpaired := by
  let count := halfProgram.comp (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength portCode (0,0))
  let cut := Procedure.unaryToBits.comp (Procedure.unaryAdd.comp (count.pair count))
  exact ((Procedure.listDrop portCode).comp (cut.pair (Procedure.identity (listCode portCode)))).congrFun
    (by intro ps; change ps.drop (ps.length/2+ps.length/2)=ps.drop (2*(ps.length/2)); rw [two_mul])

noncomputable def groupAtProgram : Procedure (prodCode unaryCode groupsCode) (listCode portCode)
    (fun x => groupAt x.2 x.1) :=
  (Procedure.listGet (listCode portCode) []).comp
    ((Procedure.unaryToBits.comp (Procedure.first unaryCode groupsCode)).pair
      (Procedure.second unaryCode groupsCode))

noncomputable def taggedPairsProgram :
    Procedure (prodCode unaryCode groupsCode) (listCode taggedCode)
      (fun x => (pairs (groupAt x.2 x.1)).map (fun p => (x.1,p))) := by
  let i := Procedure.first unaryCode groupsCode
  let ps := pairsProgram.comp groupAtProgram
  let step : Procedure (prodCode Nat.bits pairCode) taggedCode (fun x : ℕ × Pair => (x.1,x.2)) :=
    Procedure.identity taggedCode
  exact (Procedure.listMapWith (f := fun (i : ℕ) (p : Pair) => (i,p))
    ((0,0),(0,0)) (0,((0,0),(0,0))) step).comp
    ((Procedure.unaryToBits.comp i).pair ps)

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

noncomputable def countProgram : Procedure stateCode unaryCode Prod.fst := Procedure.first _ _

noncomputable def bondsProgram : Procedure stateCode (listCode MediatorListProgram.bondCode)
    (fun s => s.2.1) :=
  (Procedure.first (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode)).comp
    (Procedure.second unaryCode
      (prodCode (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode)))

noncomputable def scalarProgram : Procedure stateCode ratCode (fun s => s.2.2.1) :=
  (Procedure.first ratCode groupsCode).comp
    ((Procedure.second (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode)).comp
      (Procedure.second unaryCode
        (prodCode (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode))))

noncomputable def groupsProgram : Procedure stateCode groupsCode (fun s => s.2.2.2) :=
  (Procedure.second ratCode groupsCode).comp
    ((Procedure.second (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode)).comp
      (Procedure.second unaryCode
        (prodCode (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode))))

def scaleCode : ScaleInput → List Bool := prodCode ratCode stateCode

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

noncomputable def takeGroupsProgram : Procedure (prodCode Nat.bits groupsCode) groupsCode
    (fun x => x.2.take x.1) := by
  let n := Procedure.first Nat.bits groupsCode
  let gs := Procedure.second Nat.bits groupsCode
  let len := (Procedure.listLength (listCode portCode) []).comp gs
  let count := Procedure.binarySub.comp (len.pair n)
  let reverse := (Procedure.listReverse (listCode portCode) []).comp gs
  exact ((Procedure.listReverse (listCode portCode) []).comp
    ((Procedure.listDrop (listCode portCode)).comp (count.pair reverse))).congrFun (by
      intro x
      simp only [Function.comp_apply,← List.reverse_take,List.reverse_reverse])

noncomputable def freshPointProgram :
    Procedure (prodCode unaryCode pointCode) portCode (fun x => freshPoint x.2 x.1) := by
  let j := Procedure.unaryToBits.comp (Procedure.first unaryCode pointCode)
  let env := Procedure.second unaryCode pointCode
  let ns := (Procedure.first (prodCode Nat.bits Nat.bits) ratCode).comp env
  let n := (Procedure.first Nat.bits Nat.bits).comp ns
  let start := (Procedure.second Nat.bits Nat.bits).comp ns
  let r := (Procedure.second (prodCode Nat.bits Nat.bits) ratCode).comp env
  let offset := Procedure.binaryMul.comp
    ((Procedure.constant (prodCode unaryCode pointCode) Nat.bits 2).pair
      (Procedure.binaryAdd.comp (start.pair j)))
  exact (Procedure.binaryAdd.comp (n.pair offset)).pair r

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialProgram
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

def initialLookupCode : (ℕ × List Bond) → List Bool :=
  prodCode Nat.bits (listCode bondCode)

noncomputable def initialBondProgram : Procedure initialLookupCode bondCode
    (fun x => initialBond x.2 x.1) := by
  let j := Procedure.first Nat.bits (listCode bondCode)
  let bs := Procedure.second Nat.bits (listCode bondCode)
  let i := Procedure.binaryDiv.comp (j.pair (Procedure.constant initialLookupCode Nat.bits 2))
  exact (Procedure.listGet bondCode (0,0,0)).comp (i.pair bs)

noncomputable def initialEndpointProgram : Procedure initialLookupCode Nat.bits
    (fun x => initialEndpoint x.2 x.1) := by
  let p := initialParityProgram.comp (Procedure.first Nat.bits (listCode bondCode))
  let b := initialBondProgram
  let left := (Procedure.first Nat.bits (prodCode Nat.bits ratCode)).comp b
  let right := (Procedure.first Nat.bits ratCode).comp
    ((Procedure.second Nat.bits (prodCode Nat.bits ratCode)).comp b)
  exact (Procedure.conditional p left right).congrFun (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq,initialEndpoint])

def initialWeightCode : (ℕ × (ℚ × List Bond)) → List Bool :=
  prodCode Nat.bits (prodCode ratCode (listCode bondCode))

noncomputable def initialWeightProgram : Procedure initialWeightCode ratCode
    (fun x => initialWeight x.2.2 x.2.1 x.1) := by
  let j := Procedure.first Nat.bits (prodCode ratCode (listCode bondCode))
  let tail := Procedure.second Nat.bits (prodCode ratCode (listCode bondCode))
  let r := (Procedure.first ratCode (listCode bondCode)).comp tail
  let bs := (Procedure.second ratCode (listCode bondCode)).comp tail
  let b := initialBondProgram.comp (j.pair bs)
  let w := (Procedure.second Nat.bits ratCode).comp
    ((Procedure.second Nat.bits (prodCode Nat.bits ratCode)).comp b)
  let twice := Procedure.ratMul.comp ((Procedure.constant initialWeightCode ratCode 2).pair r)
  let odd := Procedure.ratMul.comp (twice.pair w)
  exact (Procedure.conditional (initialParityProgram.comp j) r odd).congrFun (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq,initialWeight])

noncomputable def initialMatchProgram :
    Procedure (prodCode unaryCode initialLookupCode) (listCode Nat.bits) initialMatch := by
  let j := Procedure.unaryToBits.comp (Procedure.first unaryCode initialLookupCode)
  let env := Procedure.second unaryCode initialLookupCode
  let i := (Procedure.first Nat.bits (listCode bondCode)).comp env
  let bs := (Procedure.second Nat.bits (listCode bondCode)).comp env
  let endpoint := initialEndpointProgram.comp (j.pair bs)
  let same := Procedure.binaryEq.comp (endpoint.pair i)
  let one := (Procedure.listCons Nat.bits).comp
    (j.pair (Procedure.constant _ (listCode Nat.bits) []))
  exact (Procedure.conditional same one (Procedure.constant _ (listCode Nat.bits) [])).congrFun
    (by intro x; simp only [Function.comp_apply,decide_eq_true_eq,initialMatch,id_eq])

noncomputable def initialPointProgram :
    Procedure (prodCode initialWeightCode Nat.bits) portCode
      (fun x => (x.1.1+x.2,initialWeight x.1.2.2 x.1.2.1 x.2)) := by
  let env := Procedure.first initialWeightCode Nat.bits
  let j := Procedure.second initialWeightCode Nat.bits
  let n := (Procedure.first Nat.bits (prodCode ratCode (listCode bondCode))).comp env
  let tail := (Procedure.second Nat.bits (prodCode ratCode (listCode bondCode))).comp env
  exact (Procedure.binaryAdd.comp (n.pair j)).pair (initialWeightProgram.comp (j.pair tail))

def initialGroupInputCode : (ℕ × (ℚ × (ℕ × List Bond))) → List Bool :=
  prodCode Nat.bits (prodCode ratCode initialLookupCode)

def initialGroupsCode : (ℕ × (ℚ × List Bond)) → List Bool :=
  prodCode unaryCode (prodCode ratCode (listCode bondCode))

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

def initialInputCode : InitialInput → List Bool :=
  prodCode ratCode (prodCode unaryCode (prodCode (listCode bondCode) ratCode))

noncomputable def initialInputCount : Procedure initialInputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first unaryCode (prodCode (listCode bondCode) ratCode)).comp
    (Procedure.second ratCode (prodCode unaryCode (prodCode (listCode bondCode) ratCode)))

noncomputable def initialInputBonds : Procedure initialInputCode (listCode bondCode)
    (fun x => x.2.2.1) :=
  (Procedure.first (listCode bondCode) ratCode).comp
    ((Procedure.second unaryCode (prodCode (listCode bondCode) ratCode)).comp
      (Procedure.second ratCode (prodCode unaryCode (prodCode (listCode bondCode) ratCode))))

noncomputable def initialInputConstant : Procedure initialInputCode ratCode (fun x => x.2.2.2) :=
  (Procedure.second (listCode bondCode) ratCode).comp
    ((Procedure.second unaryCode (prodCode (listCode bondCode) ratCode)).comp
      (Procedure.second ratCode (prodCode unaryCode (prodCode (listCode bondCode) ratCode))))

noncomputable def initialBondWeight : Procedure bondCode ratCode (fun b => b.2.2) :=
  (Procedure.second Nat.bits ratCode).comp (Procedure.second Nat.bits (prodCode Nat.bits ratCode))

end ContinuumCoulomb.QuantumForkList

end

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
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

def sameCell (x : Input) (i : ℕ) : Bool :=
  decide (QuantumPathVisitProgram.lookup x.2 i = QuantumPathVisitProgram.lookup x.2 x.1)

def value (x : Input) : ℕ := ((List.range x.1).map (sameCell x)).countP id

noncomputable def sameCellProgram :
    Procedure (prodCode unaryCode inputCode) Procedure.boolCode
      (fun x => sameCell x.2 x.1) := by
  let i := Procedure.unaryToBits.comp (Procedure.first unaryCode inputCode)
  let env := Procedure.second unaryCode inputCode
  let q := Procedure.unaryToBits.comp
    ((Procedure.first unaryCode (listCode pairCode)).comp env)
  let xs := (Procedure.second unaryCode (listCode pairCode)).comp env
  exact QuantumFiniteMembership.pairEqProgram.comp
    (((Procedure.listGet pairCode (0,0)).comp (i.pair xs)).pair
      ((Procedure.listGet pairCode (0,0)).comp (q.pair xs)))

noncomputable def program : Procedure inputCode unaryCode value :=
  countProgram.comp ((Procedure.tabulate (f := sameCell) false sameCellProgram).comp
    ((Procedure.first unaryCode (listCode pairCode)).pair (Procedure.identity inputCode)))

end ContinuumCoulomb.QuantumOrdinalProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialSlotProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fine-grid positions and lane colors of the ordinal-slot model
are computed directly from encoded lists of cells. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialSlotProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumOrdinalProgram

def fineSite (A : ℕ) (x : Input) : Pair :=
  let p := QuantumPathVisitProgram.lookup x.2 x.1
  (value x+A*p.1,p.2)

def lane (B : ℕ) (x : Input) : ℕ :=
  let p := QuantumPathVisitProgram.lookup x.2 x.1
  value x+B*(p.2%3)+(3*B)*(p.1%3)

noncomputable def cellProgram : Procedure inputCode pairCode
    (fun x => QuantumPathVisitProgram.lookup x.2 x.1) :=
  (Procedure.listGet pairCode (0,0)).comp
    ((Procedure.unaryToBits.comp (Procedure.first unaryCode (listCode pairCode))).pair
      (Procedure.second unaryCode (listCode pairCode)))

noncomputable def fineSiteProgram (A : ℕ) : Procedure inputCode pairCode (fineSite A) := by
  let p := cellProgram
  let row := (Procedure.first Nat.bits Nat.bits).comp p
  let col := (Procedure.second Nat.bits Nat.bits).comp p
  let rank := Procedure.unaryToBits.comp QuantumOrdinalProgram.program
  let x := Procedure.binaryAdd.comp (rank.pair
    (Procedure.binaryMul.comp ((Procedure.constant inputCode Nat.bits A).pair row)))
  exact x.pair col

noncomputable def laneProgram (B : ℕ) : Procedure inputCode Nat.bits (lane B) := by
  let p := cellProgram
  let row := (Procedure.first Nat.bits Nat.bits).comp p
  let col := (Procedure.second Nat.bits Nat.bits).comp p
  let rem (v : Procedure inputCode Nat.bits (fun x =>
      (QuantumPathVisitProgram.lookup x.2 x.1).1)) :=
    Procedure.binaryMod.comp (v.pair (Procedure.constant inputCode Nat.bits 3))
  let rowTerm := Procedure.binaryMul.comp
    ((Procedure.constant inputCode Nat.bits (3*B)).pair (rem row))
  let colTerm := Procedure.binaryMul.comp ((Procedure.constant inputCode Nat.bits B).pair
    (Procedure.binaryMod.comp (col.pair (Procedure.constant inputCode Nat.bits 3))))
  let rank := Procedure.unaryToBits.comp QuantumOrdinalProgram.program
  exact Procedure.binaryAdd.comp ((Procedure.binaryAdd.comp (rank.pair colTerm)).pair rowTerm)

end ContinuumCoulomb.QuantumSpatialSlotProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLaneUnaryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lane colors can be produced in unary without expanding the binary cell
coordinates: only their residues modulo three enter the lane formula. -/

noncomputable section
namespace ContinuumCoulomb.QuantumLaneUnaryProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumOrdinalProgram

noncomputable def program (B : ℕ) :
    Procedure inputCode unaryCode (QuantumSpatialSlotProgram.lane B) := by
  let p := QuantumSpatialSlotProgram.cellProgram
  let row := residue ((Procedure.first Nat.bits Nat.bits).comp p)
  let col := residue ((Procedure.second Nat.bits Nat.bits).comp p)
  let rowTerm := Procedure.unaryMul.comp ((Procedure.constant inputCode unaryCode (3*B)).pair row)
  let colTerm := Procedure.unaryMul.comp ((Procedure.constant inputCode unaryCode B).pair col)
  exact Procedure.unaryAdd.comp
    ((Procedure.unaryAdd.comp (QuantumOrdinalProgram.program.pair colTerm)).pair rowTerm)

end ContinuumCoulomb.QuantumLaneUnaryProgram

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
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable def belowProgram : Procedure (prodCode pairCode entryCode)
    Procedure.boolCode (fun x => below x.1 x.2) := by
  let vc := Procedure.first pairCode entryCode
  let e := Procedure.second pairCode entryCode
  let v := (Procedure.first Nat.bits Nat.bits).comp vc
  let c := (Procedure.second Nat.bits Nat.bits).comp vc
  let left := (Procedure.first Nat.bits pairCode).comp e
  let rest := (Procedure.second Nat.bits pairCode).comp e
  let right := (Procedure.first Nat.bits Nat.bits).comp rest
  let lane := (Procedure.second Nat.bits Nat.bits).comp rest
  let incident := Procedure.boolOr.comp
    ((Procedure.binaryEq.comp (left.pair v)).pair (Procedure.binaryEq.comp (right.pair v)))
  let smaller := Procedure.binaryLe.comp
    ((Procedure.binaryAdd.comp (lane.pair (Procedure.constant _ Nat.bits 1))).pair c)
  exact (Procedure.boolAnd.comp (incident.pair smaller)).congrFun (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,below]
    omega)

noncomputable def program : Procedure inputCode unaryCode value :=
  QuantumOrdinalProgram.countProgram.comp
    (Procedure.listMapWith (f := below) (0,(0,0)) false belowProgram)

end ContinuumCoulomb.QuantumPortRankProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortRankActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal incidence count computes the very arm assignment used by the
spatial routing proof, for any explicit enumeration of the interaction labels. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortRankProgram
open scoped Classical

def entries {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (i : Fin m) : Entry :=
  ((M.left (labels.symm i)).val,
    (M.right (labels.symm i)).val,(M.laneColor (labels.symm i)).val)

end ContinuumCoulomb.QuantumPortRankProgram

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

def edge (d : Data) (i : ℕ) : Pair := QuantumPathVisitProgram.lookup d.2 i
def lane (B : ℕ) (x : Input) : ℕ := QuantumSpatialSlotProgram.lane B (x.1,x.2.1.2)
def entry (B : ℕ) (d : Data) (i : ℕ) : QuantumPortRankProgram.Entry :=
  ((edge d i).1,(edge d i).2,lane B (i,d))
def entries (B : ℕ) (d : Data) : List QuantumPortRankProgram.Entry :=
  (List.range d.2.length).map (entry B d)

def fine (A : ℕ) (d : Data) (a : ℕ) : Pair :=
  QuantumSpatialSlotProgram.fineSite A (min d.1.1.length a,d.1.1)

def value (A B : ℕ) (x : Input) : QuantumBufferedListProgram.Input :=
  let e := edge x.2 x.1
  let c := lane B x
  let es := entries B x.2
  ((fine A x.2 e.1,fine A x.2 e.2),c,
    QuantumPortRankProgram.value ((e.1,c),es),
    QuantumPortRankProgram.value ((e.2,c),es))

noncomputable def edgeProgram : Procedure inputCode pairCode (fun x => edge x.2 x.1) :=
  (Procedure.listGet pairCode (0,0)).comp
    ((Procedure.unaryToBits.comp indexProgram).pair edgesProgram)

noncomputable def laneProgram (B : ℕ) : Procedure inputCode Nat.bits (lane B) :=
  (QuantumSpatialSlotProgram.laneProgram B).comp (indexProgram.pair anchorsProgram)
noncomputable def laneUnaryProgram (B : ℕ) : Procedure inputCode unaryCode (lane B) :=
  (QuantumLaneUnaryProgram.program B).comp (indexProgram.pair anchorsProgram)

noncomputable def entryProgram (B : ℕ) : Procedure inputCode QuantumPortRankProgram.entryCode
    (fun x => entry B x.2 x.1) :=
  ((Procedure.first Nat.bits Nat.bits).comp edgeProgram).pair
    (((Procedure.second Nat.bits Nat.bits).comp edgeProgram).pair (laneProgram B))

noncomputable def entriesProgram (B : ℕ) :
    Procedure dataCode (listCode QuantumPortRankProgram.entryCode) (entries B) := by
  let edges := Procedure.second (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)
  let n := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).comp edges
  exact (Procedure.tabulate (f := entry B) (0,0,0) (entryProgram B)).comp
    (n.pair (Procedure.identity dataCode))

noncomputable def program (A B : ℕ) :
    Procedure inputCode QuantumBufferedListProgram.inputCode (value A B) := by
  let left := (Procedure.first Nat.bits Nat.bits).comp edgeProgram
  let right := (Procedure.second Nat.bits Nat.bits).comp edgeProgram
  let n := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).comp qubitsProgram
  let leftIndex := Procedure.clippedUnary.comp (n.pair left)
  let rightIndex := Procedure.clippedUnary.comp (n.pair right)
  let leftPoint := (QuantumSpatialSlotProgram.fineSiteProgram A).comp (leftIndex.pair qubitsProgram)
  let rightPoint := (QuantumSpatialSlotProgram.fineSiteProgram A).comp (rightIndex.pair qubitsProgram)
  let es := (entriesProgram B).comp dataProgram
  let leftPort := QuantumPortRankProgram.program.comp ((left.pair (laneProgram B)).pair es)
  let rightPort := QuantumPortRankProgram.program.comp ((right.pair (laneProgram B)).pair es)
  exact (leftPoint.pair rightPoint).pair ((laneUnaryProgram B).pair (leftPort.pair rightPort))

end ContinuumCoulomb.QuantumRoutingInputProgram

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

noncomputable opaque entryProgram (k : ℕ) : Procedure labelsCode labelCode
    (fun xs => (xs.drop k).headD (0,0)) :=
  (Procedure.listGet labelCode (0,0)).comp
    ((Procedure.constant labelsCode Nat.bits k).pair (Procedure.identity labelsCode))
noncomputable opaque labelTest (k a : ℕ) : Procedure labelsCode Procedure.boolCode
    (fun xs => decide (((xs.drop k).headD (0,0)).2=a)) :=
  Procedure.binaryEq.comp (((Procedure.second Nat.bits Nat.bits).comp (entryProgram k)).pair
    (Procedure.constant labelsCode Nat.bits a))
noncomputable def selectedProgram (a b : ℕ) : Procedure labelsCode labelsCode
    (selected a b) :=
  (Procedure.listCons labelCode).comp ((entryProgram a).pair
    (singletonProgram _ (entryProgram b)))

noncomputable opaque partitionProgram :
    Procedure labelsCode (prodCode labelsCode labelsCode) partition := by
  let p01 := (selectedProgram 0 1).pair (singletonProgram _ (entryProgram 2))
  let p02 := (selectedProgram 0 2).pair (singletonProgram _ (entryProgram 1))
  let p12 := (selectedProgram 1 2).pair (singletonProgram _ (entryProgram 0))
  let p := Procedure.conditional (lengthTest 3)
    (Procedure.conditional (labelTest 0 2) (Procedure.conditional (labelTest 1 2) p01 p02) p12)
    ((Procedure.identity labelsCode).pair (Procedure.constant labelsCode labelsCode []))
  exact p.congrFun (by
    intro xs
    simpa only [partitionLookup,decide_eq_true_eq,id_eq] using partitionLookup_eq xs)

noncomputable opaque pairLabelsProgram : Procedure blockCode labelsCode
    (fun x => (partition x.2).1) :=
  ((Procedure.first labelsCode labelsCode).comp partitionProgram).comp labelsProgram
noncomputable opaque realLabelsProgram : Procedure blockCode labelsCode
    (fun x => (partition x.2).2) :=
  ((Procedure.second labelsCode labelsCode).comp partitionProgram).comp labelsProgram
noncomputable opaque thirdMediatorProgram : Procedure blockCode labelCode
    (fun x => (x.1,axis ((partition x.2).1.take 1))) :=
  mediatorProgram.pair (axisProgram.comp ((takeProgram 1).comp pairLabelsProgram))

noncomputable opaque thirdBlockProgram (k : Fin 7) :
    Procedure blockCode labelsCode (fun x => thirdBlock x.1 x.2 k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact Procedure.constant blockCode labelsCode []
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact singletonProgram (fun x : BlockInput => (x.1,3))
        (mediatorProgram.pair (Procedure.constant blockCode Nat.bits 3))
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact pairLabelsProgram
      · refine Fin.cases ?_ (fun k => ?_) k
        · exact realLabelsProgram
        · refine Fin.cases ?_ (fun k => ?_) k
          · exact (Procedure.listAppend labelCode (0,0)).comp
              (realLabelsProgram.pair (singletonProgram (fun x : BlockInput => (x.1,3))
                (mediatorProgram.pair (Procedure.constant blockCode Nat.bits 3))))
          · refine Fin.cases ?_ (fun k => ?_) k
            · exact (Procedure.listAppend labelCode (0,0)).comp
                (((takeProgram 1).comp pairLabelsProgram).pair
                  (singletonProgram _ thirdMediatorProgram))
            · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
              exact (Procedure.listAppend labelCode (0,0)).comp
                (((dropProgram 1).comp pairLabelsProgram).pair
                  (singletonProgram _ thirdMediatorProgram))

noncomputable opaque zerosProgram : Procedure labelsCode labelsCode zeros :=
  Procedure.listMap (0,0) (0,0) ((Procedure.first Nat.bits Nat.bits).pair
    (Procedure.constant labelCode Nat.bits 0))

noncomputable def relabelProgram (k a : ℕ) : Procedure labelsCode labelCode
    (fun xs => (((xs.drop k).headD (0,0)).1,a)) :=
  ((Procedure.first Nat.bits Nat.bits).comp (entryProgram k)).pair
    (Procedure.constant labelsCode Nat.bits a)
noncomputable def crossedProgram (a b : ℕ) : Procedure labelsCode labelsCode
    (fun xs => [(((xs.drop 0).headD (0,0)).1,a),(((xs.drop 1).headD (0,0)).1,b)]) :=
  (Procedure.listCons labelCode).comp ((relabelProgram 0 a).pair
    (singletonProgram _ (relabelProgram 1 b)))
noncomputable opaque yyFactorsProgram : Procedure labelsCode (prodCode labelsCode labelsCode)
    yyFactors := by
  let p := Procedure.conditional (Procedure.boolAnd.comp
      ((lengthTest 2).pair (labelTest 0 2)))
    ((crossedProgram 1 3).pair (crossedProgram 3 1))
    ((Procedure.identity labelsCode).pair zerosProgram)
  exact p.congrFun (by
    intro xs
    simpa only [yyLookup,Function.comp_apply,id_eq,Bool.and_eq_true,decide_eq_true_eq]
      using yyLookup_eq xs)

noncomputable opaque yyBlockProgram (k : Fin 4) :
    Procedure blockCode labelsCode (fun x => yyBlock x.1 x.2 k) := by
  let med := singletonProgram (fun x : BlockInput => (x.1,1))
    (mediatorProgram.pair (Procedure.constant blockCode Nat.bits 1))
  refine Fin.cases ?_ (fun k => ?_) k
  · exact Procedure.constant blockCode labelsCode []
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact singletonProgram (fun x : BlockInput => (x.1,3))
        (mediatorProgram.pair (Procedure.constant blockCode Nat.bits 3))
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact (Procedure.listAppend labelCode (0,0)).comp
          ((((Procedure.first labelsCode labelsCode).comp yyFactorsProgram).comp labelsProgram).pair med)
      · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
        exact (Procedure.listAppend labelCode (0,0)).comp
          ((((Procedure.second labelsCode labelsCode).comp yyFactorsProgram).comp labelsProgram).pair med)

noncomputable opaque privateBlockProgram (k : Fin 4) :
    Procedure blockCode labelsCode (fun x => privateBlock x.1 x.2 k) := by
  let med := singletonProgram (fun x : BlockInput => (x.1,1))
    (mediatorProgram.pair (Procedure.constant blockCode Nat.bits 1))
  refine Fin.cases ?_ (fun k => ?_) k
  · exact Procedure.constant blockCode labelsCode []
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact singletonProgram (fun x : BlockInput => (x.1,3))
        (mediatorProgram.pair (Procedure.constant blockCode Nat.bits 3))
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact (Procedure.listAppend labelCode (0,0)).comp ((prefixProgram 1).pair med)
      · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
        exact (Procedure.listAppend labelCode (0,0)).comp ((suffixProgram 1).pair med)

end ContinuumCoulomb.QuantumOrderedLabelData

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

def table (q : Fin n ≃ ι) (e : Fin m ≃ κ) (cell : ι → Pair) (anchor : κ → Pair) : State :=
  (List.ofFn (fun i => cell (q i)),List.ofFn (fun i => anchor (e i)))

end ContinuumCoulomb.QuantumOrderedCellTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkGridProgram
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

def cellsCode : Cells → List Bool := prodCode QuantumForkList.stateCode (listCode QuantumRouteCode.pairCode)
def queryCode : (ℕ × Cells) → List Bool := prodCode Nat.bits cellsCode
def inputCode : Input → List Bool := prodCode ratCode cellsCode

end ContinuumCoulomb.QuantumForkGridProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleProgram
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

def entryCode : Entry → List Bool := prodCode unaryCode bondCode

noncomputable opaque selectedProgram (active : Bool) :
    Procedure entryCode Procedure.boolCode (selected active) :=
  (Procedure.conditional (Procedure.unaryZero.comp (Procedure.first unaryCode bondCode))
    (Procedure.constant entryCode Procedure.boolCode (!active))
    (Procedure.constant entryCode Procedure.boolCode active)).congrFun (by intro e; simp only [Function.comp_apply,selected,decide_eq_true_eq])

noncomputable opaque eraseProgram : Procedure (listCode entryCode) (listCode bondCode) erase :=
  Procedure.listMap zeroEntry zeroBond (Procedure.second unaryCode bondCode)

def stateCode : State → List Bool := prodCode unaryCode (prodCode ratCode (listCode entryCode))
def inputCode : Input → List Bool := prodCode ratCode stateCode

noncomputable opaque stateProgram : Procedure inputCode stateCode Prod.snd := Procedure.second _ _
noncomputable opaque precisionProgram : Procedure inputCode ratCode Prod.fst := Procedure.first _ _
noncomputable opaque countInputProgram : Procedure inputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp stateProgram
noncomputable opaque tailProgram : Procedure inputCode (prodCode ratCode (listCode entryCode))
    (fun x => x.2.2) := (Procedure.second _ _).comp stateProgram
noncomputable opaque scalarInputProgram : Procedure inputCode ratCode (fun x => x.2.2.1) :=
  (Procedure.first _ _).comp tailProgram
noncomputable opaque entriesProgram : Procedure inputCode (listCode entryCode) (fun x => x.2.2.2) :=
  (Procedure.second _ _).comp tailProgram
def blockInputCode : BlockInput → List Bool :=
  prodCode QuantumListPathProgram.parametersCode (prodCode unaryCode entryCode)

noncomputable opaque blockBondInputProgram :
    Procedure blockInputCode QuantumListPathProgram.inputCode blockBondInput := by
  let p := Procedure.first QuantumListPathProgram.parametersCode (prodCode unaryCode entryCode)
  let t := Procedure.second QuantumListPathProgram.parametersCode (prodCode unaryCode entryCode)
  let i := (Procedure.first unaryCode entryCode).comp t
  let e := (Procedure.second unaryCode entryCode).comp t
  exact p.pair (i.pair ((Procedure.second unaryCode bondCode).comp e))

noncomputable opaque blockWorkProgram (k : Fin 3) :
    Procedure blockInputCode unaryCode (fun x => blockWork x k) := by
  by_cases hk : k=2
  · let p : Procedure blockInputCode unaryCode (fun x => x.2.2.1-1) :=
      Procedure.unaryPred.comp ((Procedure.first unaryCode bondCode).comp
        ((Procedure.second unaryCode entryCode).comp
          (Procedure.second QuantumListPathProgram.parametersCode (prodCode unaryCode entryCode))))
    exact p.congrFun (by intro x; simp only [blockWork,hk,ite_true, if_true])
  · exact (Procedure.constant blockInputCode unaryCode 0).congrFun
      (by intro x; simp only [blockWork,hk,ite_false, if_false])

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteProgram
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

def routedCode : Routed → List Bool := prodCode entryCode (listCode pairCode)
def stateCode : State → List Bool := prodCode QuantumListSchedule.stateCode
  (prodCode (listCode pairCode) (listCode (listCode pairCode)))
def inputCode : Input → List Bool := prodCode ratCode stateCode

noncomputable opaque precisionProgram : Procedure inputCode ratCode Prod.fst := Procedure.first _ _
noncomputable opaque dataProgram : Procedure inputCode stateCode Prod.snd := Procedure.second _ _
noncomputable opaque scheduleProgram : Procedure inputCode QuantumListSchedule.stateCode
    (fun x => x.2.1) := (Procedure.first _ _).comp dataProgram
noncomputable opaque spatialProgram : Procedure inputCode
    (prodCode (listCode pairCode) (listCode (listCode pairCode))) (fun x => x.2.2) :=
  (Procedure.second _ _).comp dataProgram
noncomputable opaque oldPositionsProgram : Procedure inputCode (listCode pairCode)
    (fun x => x.2.2.1) := (Procedure.first _ _).comp spatialProgram
noncomputable opaque oldPathsProgram : Procedure inputCode (listCode (listCode pairCode))
    (fun x => x.2.2.2) := (Procedure.second _ _).comp spatialProgram
noncomputable opaque entriesProgram : Procedure inputCode (listCode entryCode)
    (fun x => x.2.1.2.2) :=
  (Procedure.second _ _).comp ((Procedure.second _ _).comp scheduleProgram)
noncomputable opaque countProgram : Procedure inputCode unaryCode
    (fun x => x.2.1.2.2.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength entryCode zeroEntry).comp entriesProgram

noncomputable opaque indexedProgram :
    Procedure (prodCode unaryCode inputCode) routedCode indexed := by
  let k := Procedure.unaryToBits.comp (Procedure.first unaryCode inputCode)
  let x := Procedure.second unaryCode inputCode
  exact ((Procedure.listGet entryCode zeroEntry).comp (k.pair (entriesProgram.comp x))).pair
    ((Procedure.listGet (listCode pairCode) []).comp (k.pair (oldPathsProgram.comp x)))
noncomputable opaque decoratedTabProgram :
    Procedure (prodCode unaryCode inputCode) (listCode routedCode)
      (fun x => (List.range x.1).map (fun i => indexed (i,x.2))) :=
  Procedure.tabulate (f := fun x i => indexed (i,x)) (zeroEntry,[]) indexedProgram
noncomputable opaque decoratedProgram : Procedure inputCode (listCode routedCode) decorated :=
  (decoratedTabProgram.comp (countProgram.pair (Procedure.identity inputCode))).congrFun
    (by intro x; rfl)

noncomputable opaque lookupProgram (k : ℕ) :
    Procedure routedCode pairCode (fun r => lookup r.2 k) :=
  (Procedure.listGet pairCode (0,0)).comp
    ((Procedure.constant routedCode Nat.bits k).pair (Procedure.second entryCode (listCode pairCode)))

noncomputable def pairList {α : Type} (ea : α → List Bool)
    {f g : α → Pair} (p : Procedure ea pairCode f) (q : Procedure ea pairCode g) :
    Procedure ea (listCode pairCode) (fun x => [f x,g x]) :=
  (Procedure.listCons pairCode).comp (p.pair
    ((Procedure.listCons pairCode).comp (q.pair (Procedure.constant ea (listCode pairCode) []))))
noncomputable opaque freshProgram : Procedure routedCode (listCode pairCode) freshPoints :=
  pairList routedCode (lookupProgram 1) (lookupProgram 2)
noncomputable opaque pathBlockProgram : Procedure routedCode (listCode (listCode pairCode)) pathBlock := by
  let first := freshProgram
  let second := pairList routedCode (lookupProgram 0) (lookupProgram 1)
  let third := (Procedure.listReverse pairCode (0,0)).comp
    ((Procedure.listDrop pairCode).comp
      ((Procedure.constant routedCode Nat.bits 2).pair
        (Procedure.second entryCode (listCode pairCode))))
  exact (Procedure.listCons (listCode pairCode)).comp (first.pair
    ((Procedure.listCons (listCode pairCode)).comp (second.pair
      ((Procedure.listCons (listCode pairCode)).comp
        (third.pair (Procedure.constant routedCode (listCode (listCode pairCode)) []))))))

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRouteLeafProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial TM2 evaluators for scaled centers and reserved leaves. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRouteLeafCode
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable def coordinateProgram (xAxis : Bool) (offset : ℕ) : Procedure pairCode Nat.bits
    (fun p => 8*(if xAxis then p.1 else p.2)+offset) := by
  let p : Procedure pairCode Nat.bits (fun p => if xAxis then p.1 else p.2) := by
    cases xAxis
    · exact Procedure.second Nat.bits Nat.bits
    · exact Procedure.first Nat.bits Nat.bits
  let mul := Procedure.binaryMul.comp ((Procedure.constant pairCode Nat.bits 8).pair p)
  exact (Procedure.binaryAdd.comp (mul.pair (Procedure.constant pairCode Nat.bits offset))).congrFun
    (by intro p; cases xAxis <;> rfl)

noncomputable opaque centerProgram : Procedure pairCode pairCode qmaLeafCenter :=
  (coordinateProgram true 4).pair (coordinateProgram false 4)

noncomputable def leafProgram (a : Fin 4) : Procedure pairCode pairCode (fun p => qmaRouteLeaf p a) := by
  by_cases h0 : a = 0
  · subst a
    exact ((coordinateProgram true 5).pair (coordinateProgram false 5)).congrFun (by intro p; rfl)
  by_cases h1 : a = 1
  · subst a
    exact ((coordinateProgram true 3).pair (coordinateProgram false 5)).congrFun (by intro p; rfl)
  by_cases h2 : a = 2
  · subst a
    exact ((coordinateProgram true 3).pair (coordinateProgram false 3)).congrFun (by intro p; rfl)
  have h3 : a = 3 := by omega
  subst a
  exact ((coordinateProgram true 5).pair (coordinateProgram false 3)).congrFun (by intro p; rfl)

noncomputable opaque directionProgram : Procedure endsCode Nat.bits
    (fun x => (qmaGridNeighborIndex x.1 x.2).val) := by
  let one := Procedure.constant endsCode Nat.bits 1
  let east := Procedure.binaryEq.comp ((axisProgram false true).pair
    (Procedure.binaryAdd.comp ((axisProgram true true).pair one)))
  let north := Procedure.binaryEq.comp ((axisProgram false false).pair
    (Procedure.binaryAdd.comp ((axisProgram true false).pair one)))
  let west := Procedure.binaryEq.comp ((Procedure.binaryAdd.comp ((axisProgram false true).pair one)).pair
    (axisProgram true true))
  exact (Procedure.conditional east (Procedure.constant endsCode Nat.bits 0)
    (Procedure.conditional north (Procedure.constant endsCode Nat.bits 1)
      (Procedure.conditional west (Procedure.constant endsCode Nat.bits 2)
        (Procedure.constant endsCode Nat.bits 3)))).congrFun
      (by intro x; simp [qmaGridNeighborIndex]; split_ifs <;> rfl)

noncomputable opaque selectedLeafProgram : Procedure endsCode pairCode
    (fun x => qmaRouteLeaf x.1 (qmaGridNeighborIndex x.1 x.2)) := by
  let isZero := Procedure.binaryEq.comp (directionProgram.pair (Procedure.constant endsCode Nat.bits 0))
  let isOne := Procedure.binaryEq.comp (directionProgram.pair (Procedure.constant endsCode Nat.bits 1))
  let isTwo := Procedure.binaryEq.comp (directionProgram.pair (Procedure.constant endsCode Nat.bits 2))
  exact (Procedure.conditional isZero ((leafProgram 0).comp firstProgram)
    (Procedure.conditional isOne ((leafProgram 1).comp firstProgram)
      (Procedure.conditional isTwo ((leafProgram 2).comp firstProgram)
        ((leafProgram 3).comp firstProgram)))).congrFun (by
          intro x
          generalize h : qmaGridNeighborIndex x.1 x.2 = a
          fin_cases a <;> simp [h])

end ContinuumCoulomb.QuantumRouteLeafCode

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

def point (x : Input) : Pair := qmaInflatedPoint (QuantumForkGridProgram.lookup x.2) x.1
def value (xs : List Pair) : List Pair :=
  (List.range (8*(xs.length-1)+1)).map (fun k => point (k,xs))

noncomputable opaque lengthProgram : Procedure (listCode pairCode) unaryCode
    (fun xs => 8*(xs.length-1)+1) :=
  Procedure.unarySuccessor.comp (Procedure.unaryMul.comp
    ((Procedure.constant (listCode pairCode) unaryCode 8).pair
      (Procedure.unaryPred.comp
        (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)))))

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

def fresh (xs : List Pair) : List Pair :=
  [QuantumInflatedListProgram.point (1,xs),leaf xs]
def paths (xs : List Pair) : List (List Pair) :=
  [fresh xs,[QuantumInflatedListProgram.point (0,xs),
    QuantumInflatedListProgram.point (1,xs)],
    ((QuantumInflatedListProgram.value xs).drop 1).reverse]

noncomputable opaque leafProgram : Procedure (listCode pairCode) pairCode leaf := by
  let get (k : ℕ) := (Procedure.listGet pairCode (0,0)).comp
    ((Procedure.constant (listCode pairCode) Nat.bits k).pair
      (Procedure.identity (listCode pairCode)))
  exact QuantumRouteLeafCode.selectedLeafProgram.comp ((get 0).pair (get 1))

noncomputable def pairList {α : Type} (ea : α → List Bool)
    {f g : α → Pair} (p : Procedure ea pairCode f) (q : Procedure ea pairCode g) :
    Procedure ea (listCode pairCode) (fun x => [f x,g x]) :=
  (Procedure.listCons pairCode).comp (p.pair
    ((Procedure.listCons pairCode).comp (q.pair (Procedure.constant ea (listCode pairCode) []))))

end ContinuumCoulomb.QuantumEvenListPieces

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListSchedule
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Validity, fixed-round termination and full-space energy bounds for the
literal list-work routing compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open Matrix MediatorListProgram

theorem partition_zero (xs : List Entry) (e : Entry) (he : e ∈ partition false xs) : e.1=0 := by
  have h := (List.mem_filter.mp he).2
  by_contra hn
  simp [selected,hn] at h

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListMergeProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

def inputCode : Input → List Bool := prodCode unaryCode (listCode bondCode)

noncomputable def orderedProgram : Procedure bondCode pairCode ordered := by
  let a := Procedure.first Nat.bits (prodCode Nat.bits ratCode)
  let b := (Procedure.first Nat.bits ratCode).comp
    (Procedure.second Nat.bits (prodCode Nat.bits ratCode))
  let h := Procedure.binaryLe.comp (a.pair b)
  exact ((Procedure.conditional h a b).pair (Procedure.conditional h b a)).congrFun (by
    intro e
    by_cases he : e.1 ≤ e.2.1
    · simp [ordered,he]
    · have hge : e.2.1 ≤ e.1 := by omega
      simp [ordered,he,hge])

noncomputable def rowProgram : Procedure (prodCode unaryCode Nat.bits) (listCode pairCode)
    (fun x => (List.range x.1).map (fun j => (x.2,j))) :=
  Procedure.tabulate (f := fun i j => (i,j)) (0,0)
    ((Procedure.second unaryCode Nat.bits).pair
      (Procedure.unaryToBits.comp (Procedure.first unaryCode Nat.bits)))

noncomputable def weightProgram : Procedure (prodCode pairCode (listCode bondCode)) ratCode
    (fun x => weight x.2 x.1) := by
  let p := Procedure.first pairCode bondCode
  let e := Procedure.second pairCode bondCode
  let h := QuantumFiniteMembership.pairEqProgram.comp ((orderedProgram.comp e).pair p)
  let w := (Procedure.second Nat.bits ratCode).comp
    ((Procedure.second Nat.bits (prodCode Nat.bits ratCode)).comp e)
  let one : Procedure (prodCode pairCode bondCode) ratCode
      (fun x => if ordered x.2=x.1 then x.2.2.2 else 0) :=
    (Procedure.conditional h w (Procedure.constant _ ratCode 0)).congrFun (by
      intro x
      simp only [Function.comp_apply,decide_eq_true_eq])
  exact RationalSumProgram.sumProgram.comp
    (Procedure.listMapWith (ea := pairCode) (eb := bondCode) (ec := ratCode)
      (f := fun p e => if ordered e=p then e.2.2 else 0) zeroBond 0 one)

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

noncomputable section

noncomputable def indexProgram (k : ℕ) :
    Procedure (listCode Procedure.boolCode) Nat.bits (firstTrue k) := by
  induction k with
  | zero => exact Procedure.constant _ _ 0
  | succ k ih =>
    let head := Procedure.listHead Procedure.boolCode false
    let tail := Procedure.listTail Procedure.boolCode
    let next := Procedure.binaryAdd.comp
      ((Procedure.constant (listCode Procedure.boolCode) Nat.bits 1).pair (ih.comp tail))
    exact (Procedure.conditional head (Procedure.constant _ _ 0) next).congrFun (by intro bs; rfl)

end
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

noncomputable def selectParallelProgram {β : Type} (eb : β → List Bool) (default : β) :
    Procedure (prodCode (listCode eb) (listCode Procedure.boolCode)) eb
      (selectParallelValue default) :=
  (Procedure.listGet eb default).comp
    (((indexProgram 140).comp (Procedure.second _ _)).pair (Procedure.first _ _))

end ContinuumCoulomb.QuantumFiniteRouteSearch

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTaggedRouteProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

noncomputable def append {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (d : β) {f g : α → List β} (p : Procedure ea (listCode eb) f)
    (q : Procedure ea (listCode eb) g) : Procedure ea (listCode eb) (fun x => f x++g x) :=
  (Procedure.listAppend eb d).comp (p.pair q)

noncomputable def fixedFlat {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (d : β) (m : ℕ) (f : Fin m → α → List β)
    (p : ∀ i, Procedure ea (listCode eb) (f i)) :
    Procedure ea (listCode eb) (fun x => (List.ofFn (fun i => f i x)).flatten) := by
  induction m with
  | zero => exact (Procedure.constant _ _ []).congrFun (by intro x; simp)
  | succ m ih =>
    exact (append ea eb d (p 0) (ih (fun i => f i.succ) (fun i => p i.succ))).congrFun (by
      intro x
      simp only [List.ofFn_succ,List.flatten_cons])

noncomputable opaque orientedProgram : Procedure taggedCode (listCode taggedCode)
    (fun x => oriented x.1 x.2) := by
  let same := Procedure.identity taggedCode
  let rev := (Procedure.first Procedure.boolCode (listCode pairCode)).pair
    ((Procedure.listReverse pairCode (0,0)).comp
      (Procedure.second Procedure.boolCode (listCode pairCode)))
  exact (Procedure.listCons taggedCode).comp (same.pair
    ((Procedure.listCons taggedCode).comp
      (rev.pair (Procedure.constant taggedCode (listCode taggedCode) []))))

noncomputable def bodyProgram (B : Pair → QMACellRouteBody)
    (p : Procedure inputCode (listCode pairCode) (fun x => (B x.2).path))
    (q : Procedure inputCode Procedure.boolCode (fun x => bodyPermitted x.1 (B x.2))) :
    Procedure inputCode (listCode taggedCode)
      (fun x => oriented (bodyPermitted x.1 (B x.2)) ((B x.2).path)) :=
  orientedProgram.comp (q.pair p)

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

noncomputable opaque matchProgram : Procedure (prodCode endsCode taggedCode) Procedure.boolCode
    (fun x => accepts x.1 x.2) := by
  let ends := Procedure.first endsCode taggedCode
  let tag := Procedure.second endsCode taggedCode
  let bit := (Procedure.first Procedure.boolCode (listCode pairCode)).comp tag
  let path := (Procedure.second Procedure.boolCode (listCode pairCode)).comp tag
  let head := (Procedure.listHead pairCode (0,0)).comp path
  let last := (Procedure.listHead pairCode (0,0)).comp
    ((Procedure.listReverse pairCode (0,0)).comp path)
  let left := QuantumFiniteMembership.pairEqProgram.comp
    (head.pair ((Procedure.first pairCode pairCode).comp ends))
  let right := QuantumFiniteMembership.pairEqProgram.comp
    (last.pair ((Procedure.second pairCode pairCode).comp ends))
  exact Procedure.boolAnd.comp ((Procedure.boolAnd.comp (bit.pair left)).pair right)

noncomputable opaque chooseProgram : Procedure (prodCode endsCode (listCode taggedCode))
    (listCode pairCode) choose := by
  let bits := Procedure.listMapWith (false,[]) false matchProgram
  let tags := Procedure.second endsCode (listCode taggedCode)
  let chosen := (selectParallelProgram taggedCode (false,[])).comp (tags.pair bits)
  exact (Procedure.second Procedure.boolCode (listCode pairCode)).comp chosen

def candidates (x : Input) : List Tagged :=
  (qmaRouteCandidates x.2.1 x.2.2).map (tagged x.1)

def value (x : Input) : List Pair := choose (x.2,candidates x)

end ContinuumCoulomb.QuantumRouteSelectorProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkGridInitial
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

def initialCellsCode : InitialCells → List Bool :=
  prodCode unaryCode (prodCode (listCode bondCode) (listCode QuantumRouteCode.pairCode))
def initialQueryCode : (ℕ × InitialCells) → List Bool := prodCode Nat.bits initialCellsCode

noncomputable def initialCellProgram : Procedure initialQueryCode QuantumRouteCode.pairCode
    (fun x => initialCell x.2.1 x.2.2.1 (lookup x.2.2.2) x.1) := by
  let v := Procedure.first Nat.bits initialCellsCode
  let env := Procedure.second Nat.bits initialCellsCode
  let n := Procedure.unaryToBits.comp ((Procedure.first unaryCode
    (prodCode (listCode bondCode) (listCode QuantumRouteCode.pairCode))).comp env)
  let tail := (Procedure.second unaryCode
    (prodCode (listCode bondCode) (listCode QuantumRouteCode.pairCode))).comp env
  let bs := (Procedure.first (listCode bondCode) (listCode QuantumRouteCode.pairCode)).comp tail
  let cells := (Procedure.second (listCode bondCode) (listCode QuantumRouteCode.pairCode)).comp tail
  let endpoint := initialEndpointProgram.comp ((Procedure.binarySub.comp (v.pair n)).pair bs)
  let target := Procedure.conditional (Procedure.binaryLt.comp (v.pair n)) v endpoint
  exact ((Procedure.listGet QuantumRouteCode.pairCode (0,0)).comp (target.pair cells)).congrFun (by
    intro x
    change lookup x.2.2.2 (if decide (x.1<x.2.1) then x.1 else
      initialEndpoint x.2.2.1 (x.1-x.2.1)) = _
    unfold initialCell
    by_cases h : x.1<x.2.1 <;> simp [h])

noncomputable def initialCellsProgram :
    Procedure initialCellsCode (listCode QuantumRouteCode.pairCode) initialCells := by
  let n := Procedure.first unaryCode
    (prodCode (listCode bondCode) (listCode QuantumRouteCode.pairCode))
  let bs := (Procedure.first (listCode bondCode) (listCode QuantumRouteCode.pairCode)).comp
    (Procedure.second unaryCode (prodCode (listCode bondCode) (listCode QuantumRouteCode.pairCode)))
  let len := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode (0,0,0)).comp bs
  let count := Procedure.unaryAdd.comp (n.pair (Procedure.unaryAdd.comp (len.pair len)))
  let query : Procedure (prodCode unaryCode initialCellsCode) initialQueryCode
      (fun x => (x.1,x.2)) :=
    (Procedure.unaryToBits.comp (Procedure.first unaryCode initialCellsCode)).pair
      (Procedure.second unaryCode initialCellsCode)
  exact ((Procedure.tabulate (f := fun x i => initialCell x.1 x.2.1 (lookup x.2.2) i)
    (0,0) (initialCellProgram.comp query)).comp
      (count.pair (Procedure.identity initialCellsCode))).congrFun (by
        intro x
        change (List.range (x.1+(x.2.1.length+x.2.1.length))).map _=initialCells x
        simp only [initialCells,two_mul,id_eq])

def preparedCode : PreparedInput → List Bool :=
  prodCode initialInputCode (listCode QuantumRouteCode.pairCode)

end ContinuumCoulomb.QuantumForkGridProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridMidpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer midpoints choose a common neighboring cell deterministically.
Their coordinate map has a literal polynomial register program. -/

noncomputable section
namespace ContinuumCoulomb
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

namespace QuantumGridMidpoint

noncomputable def program : Procedure (prodCode pairCode pairCode) pairCode value := by
  let p := Procedure.first pairCode pairCode
  let q := Procedure.second pairCode pairCode
  let first := Procedure.first Nat.bits Nat.bits
  let second := Procedure.second Nat.bits Nat.bits
  let two := Procedure.constant (prodCode pairCode pairCode) Nat.bits 2
  let row := Procedure.binaryDiv.comp
    ((Procedure.binaryAdd.comp ((first.comp p).pair (first.comp q))).pair two)
  let col := Procedure.binaryDiv.comp
    ((Procedure.binaryAdd.comp ((second.comp p).pair (second.comp q))).pair two)
  exact row.pair col

end QuantumGridMidpoint
end ContinuumCoulomb

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

def fullGraph (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) (hn : ∀ b ∈ s.2.1, b.1≠b.2.1) :=
  QuantumListGraph.ofBonds s.1 (fullList s) s.2.2.1
    (fullList_bounded s hs hb) (fullList_noLoops s hs hn)

end ContinuumCoulomb.QuantumForkList

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

noncomputable def starProgram : Procedure (prodCode Nat.bits portCode) bondCode star :=
  Procedure.identity bondCode

noncomputable def starBondsProgram :
    Procedure (prodCode unaryCode groupsCode) (listCode bondCode)
      (fun x => starBonds x.1 (groupAt x.2 x.1)) := by
  let i := Procedure.unaryToBits.comp (Procedure.first unaryCode groupsCode)
  let ps := groupAtProgram
  exact ((Procedure.listMapWith (f := fun i p => star (i,p)) (0,0) (0,0,0) starProgram).comp
    (i.pair ps)).congrFun (by intro x; rfl)

noncomputable def endpointProgram : Procedure bondCode QuantumRouteCode.pairCode endpoint :=
  (Procedure.first Nat.bits (prodCode Nat.bits ratCode)).pair
    ((Procedure.first Nat.bits ratCode).comp (Procedure.second Nat.bits (prodCode Nat.bits ratCode)))

def queryCode : Query → List Bool := prodCode bondCode (listCode QuantumRouteCode.pairCode)

noncomputable def anchorProgram : Procedure queryCode QuantumRouteCode.pairCode anchor := by
  let b := Procedure.first bondCode (listCode QuantumRouteCode.pairCode)
  let cells := Procedure.second bondCode (listCode QuantumRouteCode.pairCode)
  let ends := endpointProgram.comp b
  let left := (Procedure.first Nat.bits Nat.bits).comp ends
  let right := (Procedure.second Nat.bits Nat.bits).comp ends
  let get := Procedure.listGet QuantumRouteCode.pairCode (0,0)
  exact QuantumGridMidpoint.program.comp
    ((get.comp (left.pair cells)).pair (get.comp (right.pair cells)))

end ContinuumCoulomb.QuantumForkRoutingData

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual edge-indexed schedule represented by a literal bond/work tape. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open MediatorListProgram
open scoped Classical

def retainedEquiv (s : State) (hs : Valid s) :
    Fin (partition false s.2.2).length ≃ {i : (graph s hs).Edge // i ∉ (schedule s hs).active} :=
  (indexEquiv false s.2.2).trans (Equiv.subtypeEquivRight (fun i => by
    apply (selected_false_iff (s.2.2.get i)).trans
    have hn : (s.2.2.get i).1=0 ↔ ¬0<(s.2.2.get i).1 := by omega
    exact hn.trans (not_congr (schedule_active s hs i)).symm))

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleLabels
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.mem_crossingCells _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_fresh _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected-list ordering gives an explicit correspondence with the
abstract schedule's fresh spins. Retained source spins keep their labels. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open MediatorGraph

theorem retained_source (s : State) (hs : Valid s) (i : Fin (partition false s.2.2).length) :
    s.2.2.get (retainedEquiv s hs i).val=(partition false s.2.2).get i :=
  indexEquiv_get false s.2.2 i

def vertexRelabel (s : State) (hs : Valid s) :
    Fin (s.1+(partition true s.2.2).length*2) ≃ Fin (s.1+(schedule s hs).active.card*2) :=
  ((vertexEquiv s.1 (partition true s.2.2).length).symm.trans
    (Equiv.sumCongr (Equiv.refl (Fin s.1))
      (Equiv.prodCongr (activePermutation s hs) (Equiv.refl (Fin 2))))).trans
        (vertexEquiv s.1 (schedule s hs).active.card)

theorem vertexRelabel_old (s : State) (hs : Valid s) (v : Fin s.1) :
    vertexRelabel s hs (old s.1 (partition true s.2.2).length v) =
      old s.1 (schedule s hs).active.card v := by
  simp [vertexRelabel,old]

theorem vertexRelabel_fresh (s : State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) (a : Fin 2) :
    vertexRelabel s hs (fresh s.1 (partition true s.2.2).length i a) =
      fresh s.1 (schedule s hs).active.card (activePermutation s hs i) a := by
  simp [vertexRelabel,fresh]

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact edge order in the emitted next-round list: retained edges followed
by three consecutive edges for each selected source edge. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open MediatorListProgram

def tagValue (x : Input) : Tags x → Entry
  | .inl i => (partition false x.2.2.2).get i
  | .inr (i,k) => (blockWork (indexed (i.val,x)) k,
      QuantumListPathProgram.bond (blockBondInput (indexed (i.val,x))) k)

theorem ofFn_triples {m : ℕ} (f : Fin m × Fin 3 → Entry) :
    List.ofFn (fun k : Fin (m*3) => f (finProdFinEquiv.symm k)) =
      (List.ofFn fun i : Fin m => List.ofFn fun k : Fin 3 => f (i,k)).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg (fun g : Fin m → List Entry => List.ofFn g)
  funext i
  apply congrArg (fun g : Fin 3 → Entry => List.ofFn g)
  funext k
  have he : (⟨i.val*3+k.val,by omega⟩ : Fin (m*3))=finProdFinEquiv (i,k) := by
    apply Fin.ext
    change i.val*3+k.val=k.val+3*i.val
    omega
  rw [he,Equiv.symm_apply_apply]

theorem value_ofFn (x : Input) :
    (value x).2.2 = List.ofFn (fun i => tagValue x (flatTagEquiv x i)) := by
  rw [List.ofFn_add]
  change _ = (List.ofFn (fun i : Fin (partition false x.2.2.2).length =>
    tagValue x (flatTagEquiv x (Fin.castAdd ((partition true x.2.2.2).length*3) i))))++
    List.ofFn (fun i : Fin ((partition true x.2.2.2).length*3) =>
      tagValue x (flatTagEquiv x (Fin.natAdd (partition false x.2.2.2).length i)))
  simp only [flatTagEquiv,Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd,Equiv.sumCongr_apply,Equiv.refl_apply,
    Sum.map_inl,Sum.map_inr,tagValue]
  rw [List.ofFn_get]
  have h3 := ofFn_triples (fun p : Fin (partition true x.2.2.2).length × Fin 3 =>
    (blockWork (indexed (p.1.val,x)) p.2,
      QuantumListPathProgram.bond (blockBondInput (indexed (p.1.val,x))) p.2))
  rw [h3]
  change partition false x.2.2.2++family x = _
  rw [family_ofFn]
  rfl

theorem value_length (x : Input) : (value x).2.2.length =
    (partition false x.2.2.2).length+(partition true x.2.2.2).length*3 := by
  change (partition false x.2.2.2++family x).length = _
  rw [List.length_append,family_length]

def tagEquiv (x : Input) : Fin (value x).2.2.length ≃ Tags x :=
  (finCongr (value_length x)).trans (flatTagEquiv x)

theorem tagEquiv_get (x : Input) (i : Fin (value x).2.2.length) :
    (value x).2.2.get i=tagValue x (tagEquiv x i) := by
  have hi : i.val<(partition false x.2.2.2).length+(partition true x.2.2.2).length*3 := by
    rw [← value_length]
    exact i.isLt
  have h := congrArg (fun xs : List Entry => xs[i.val]?) (value_ofFn x)
  have hc : Fin.cast (value_length x) i = ⟨i.val,hi⟩ := Fin.ext rfl
  change (value x).2.2.get i = tagValue x (flatTagEquiv x (Fin.cast (value_length x) i))
  rw [hc]
  simpa only [List.getElem?_eq_getElem i.isLt,List.getElem?_ofFn,dite_eq_left hi,
    Option.some.injEq,List.get_eq_getElem] using h

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleGeometry
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.mem_crossingCells _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_fresh _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

def nextEdge (x : Input) (hs : Valid x.2) :
    (schedule (value x) (value_valid x hs)).graph.Edge ≃
      ((schedule x.2 hs).next x.1).graph.Edge :=
  (tagEquiv x).trans (Equiv.sumCongr (retainedEquiv x.2 hs)
    (roleEquiv (activePermutation x.2 hs)))

theorem value_count (x : Input) :
    (value x).1=x.2.1+(partition true x.2.2.2).length*2 := by
  simp only [value,QuantumListPathStep.count,stepInput,erase,List.length_map]

def nextVertex (x : Input) (hs : Valid x.2) :
    Fin (schedule (value x) (value_valid x hs)).graph.n ≃
      Fin ((schedule x.2 hs).next x.1).graph.n :=
  (finCongr (value_count x)).trans (vertexRelabel x.2 hs)

theorem indexed_entry (x : Input) (i : Fin (partition true x.2.2.2).length) :
    (indexed (i.val,x)).2.2=(partition true x.2.2.2).get i := by
  change ((partition true x.2.2.2).drop i.val).headD zeroEntry = _
  rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem i.isLt]
  rfl

theorem indexed_bond (x : Input) (i : Fin (partition true x.2.2.2).length) :
    blockBondInput (indexed (i.val,x)) =
      (QuantumListPathStep.parameters (stepInput x),i.val,((partition true x.2.2.2).get i).2) := by
  change (QuantumListPathStep.parameters (stepInput x),i.val,(indexed (i.val,x)).2.2.2) = _
  rw [indexed_entry]

def tagLeft (x : Input) (hs : Valid x.2) : Tags x →
    Fin (x.2.1+(partition true x.2.2.2).length*2)
  | .inl i => old _ _ ((graph x.2 hs).left (retainedEquiv x.2 hs i).val)
  | .inr (i,k) => ![fresh _ _ i 0,
      old _ _ ((graph x.2 hs).left (qmaSelectedIndex (schedule x.2 hs).active (activePermutation x.2 hs i))),
      old _ _ ((graph x.2 hs).right (qmaSelectedIndex (schedule x.2 hs).active (activePermutation x.2 hs i)))] k

def tagRight (x : Input) (hs : Valid x.2) : Tags x →
    Fin (x.2.1+(partition true x.2.2.2).length*2)
  | .inl i => old _ _ ((graph x.2 hs).right (retainedEquiv x.2 hs i).val)
  | .inr (i,k) => ![fresh _ _ i 1,fresh _ _ i 0,fresh _ _ i 1] k

theorem left_tag (x : Input) (hs : Valid x.2) (t : Tags x) :
    finCongr (value_count x)
        ((graph (value x) (value_valid x hs)).left ((tagEquiv x).symm t)) =
      tagLeft x hs t := by
  apply Fin.ext
  change ((value x).2.2.get ((tagEquiv x).symm t)).2.1 = _
  rw [tagEquiv_get,Equiv.apply_symm_apply]
  rcases t with i | ⟨i,k⟩
  · change ((partition false x.2.2.2).get i).2.1 = _
    simpa only [tagLeft,oldValue,graph] using
      (congrArg (fun e : Entry => e.2.1) (retained_source x.2 hs i)).symm
  · have he := active_source x.2 hs i
    simp only [List.get_eq_getElem] at he
    fin_cases k <;>
      simp [tagValue,tagLeft,QuantumListPathProgram.bond,QuantumListPathProgram.left,
        indexed_bond,QuantumListPathStep.parameters,stepInput,graph,
        oldValue,freshValue,he]

theorem right_tag (x : Input) (hs : Valid x.2) (t : Tags x) :
    finCongr (value_count x)
        ((graph (value x) (value_valid x hs)).right ((tagEquiv x).symm t)) =
      tagRight x hs t := by
  apply Fin.ext
  change ((value x).2.2.get ((tagEquiv x).symm t)).2.2.1 = _
  rw [tagEquiv_get,Equiv.apply_symm_apply]
  rcases t with i | ⟨i,k⟩
  · change ((partition false x.2.2.2).get i).2.2.1 = _
    simpa only [tagRight,oldValue,graph] using
      (congrArg (fun e : Entry => e.2.2.1) (retained_source x.2 hs i)).symm
  · fin_cases k <;>
      simp [tagValue,tagRight,QuantumListPathProgram.bond,QuantumListPathProgram.right,
        indexed_bond,QuantumListPathStep.parameters,stepInput,
        freshValue]

def tagEdge (x : Input) (hs : Valid x.2) : Tags x →
    QMAPartialPathsEdge (schedule x.2 hs).active
  | .inl i => .inl (retainedEquiv x.2 hs i)
  | .inr p => .inr (role (activePermutation x.2 hs) p)

theorem nextEdge_eq (x : Input) (hs : Valid x.2) (i : Fin (value x).2.2.length) :
    nextEdge x hs i=tagEdge x hs (tagEquiv x i) := by
  change (Equiv.sumCongr (retainedEquiv x.2 hs)
    (roleEquiv (activePermutation x.2 hs))) (tagEquiv x i) = _
  generalize tagEquiv x i=t
  rcases t with i | ⟨i,k⟩ <;> rfl

theorem tag_left_relabel (x : Input) (hs : Valid x.2) (t : Tags x) :
    vertexRelabel x.2 hs (tagLeft x hs t) =
      ((schedule x.2 hs).next x.1).graph.left (tagEdge x hs t) := by
  rcases t with i | ⟨i,k⟩
  · exact vertexRelabel_old _ _ _
  · fin_cases k
    · exact vertexRelabel_fresh _ _ _ _
    · exact vertexRelabel_old _ _ _
    · exact vertexRelabel_old _ _ _

theorem tag_right_relabel (x : Input) (hs : Valid x.2) (t : Tags x) :
    vertexRelabel x.2 hs (tagRight x hs t) =
      ((schedule x.2 hs).next x.1).graph.right (tagEdge x hs t) := by
  rcases t with i | ⟨i,k⟩
  · exact vertexRelabel_old _ _ _
  · fin_cases k
    · exact vertexRelabel_fresh _ _ _ _
    · exact vertexRelabel_fresh _ _ _ _
    · exact vertexRelabel_fresh _ _ _ _

theorem work_tag (x : Input) (hs : Valid x.2) (t : Tags x) :
    (tagValue x t).1=((schedule x.2 hs).next x.1).work (tagEdge x hs t) := by
  rcases t with i | ⟨i,k⟩
  · exact partition_zero _ _ (List.get_mem _ i)
  · fin_cases k
    · rfl
    · rfl
    · change (indexed (i.val,x)).2.2.1-1 =
        (x.2.2.2.get (qmaSelectedIndex (schedule x.2 hs).active (activePermutation x.2 hs i))).1-1
      rw [indexed_entry]
      exact congrArg (fun e : Entry => e.1-1) (active_source x.2 hs i).symm

theorem next_left (x : Input) (hs : Valid x.2) (i : Fin (value x).2.2.length) :
    nextVertex x hs ((graph (value x) (value_valid x hs)).left i) =
      ((schedule x.2 hs).next x.1).graph.left (nextEdge x hs i) := by
  rw [nextEdge_eq]
  have h : finCongr (value_count x) ((graph (value x) (value_valid x hs)).left i) =
      tagLeft x hs (tagEquiv x i) := by
    simpa only [Equiv.symm_apply_apply] using left_tag x hs (tagEquiv x i)
  exact (congrArg (vertexRelabel x.2 hs) h).trans (tag_left_relabel x hs (tagEquiv x i))

theorem next_right (x : Input) (hs : Valid x.2) (i : Fin (value x).2.2.length) :
    nextVertex x hs ((graph (value x) (value_valid x hs)).right i) =
      ((schedule x.2 hs).next x.1).graph.right (nextEdge x hs i) := by
  rw [nextEdge_eq]
  have h : finCongr (value_count x) ((graph (value x) (value_valid x hs)).right i) =
      tagRight x hs (tagEquiv x i) := by
    simpa only [Equiv.symm_apply_apply] using right_tag x hs (tagEquiv x i)
  exact (congrArg (vertexRelabel x.2 hs) h).trans (tag_right_relabel x hs (tagEquiv x i))

theorem next_work (x : Input) (hs : Valid x.2) (i : Fin (value x).2.2.length) :
    (schedule (value x) (value_valid x hs)).work i =
      ((schedule x.2 hs).next x.1).work (nextEdge x hs i) := by
  change ((value x).2.2.get i).1 = _
  rw [tagEquiv_get,nextEdge_eq]
  exact work_tag x hs (tagEquiv x i)

def nextRelabel (x : Input) (hs : Valid x.2) :
    QMAPathRelabeling (schedule (value x) (value_valid x hs))
      ((schedule x.2 hs).next x.1) where
  vertex := nextVertex x hs
  edge := nextEdge x hs
  left := next_left x hs
  right := next_right x hs
  work := next_work x hs

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListScheduleRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-list schedule: route preservation and nearest-neighbor
realization after the prescribed number of rounds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open scoped Classical

variable {Γ : SimpleGraph (ℕ × ℕ)}

def nextEmbedding (x : Input) (hs : Valid x.2)
    (P : QMAPathEmbedding (schedule x.2 hs) Γ) :
    QMAPathEmbedding (schedule (value x) (value_valid x hs)) Γ :=
  (nextRelabel x hs).symm.transport (P.next x.1)

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialInputTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed fork-state/cell tape is exactly the array of the spatial
model. Only cells at actual spin indices are read. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialInputTape
open QuantumForkList QuantumForkGridProgram QuantumRouteCode

def coordinates {rows width : ℕ} (p : QMAGridCell rows width) : QuantumRouteCode.Pair :=
  (p.1.val,p.2.val)

def input {rows width A D : ℕ} (I : SpatialInput rows width A D) : PreparedInput :=
  ((I.precision,I.n,I.bonds,I.constant),List.ofFn (fun v : Fin I.n => coordinates (I.cell v.val)))

end ContinuumCoulomb.QuantumSpatialInputTape

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

def state (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m)
    (work : G.Edge → ℕ) : State :=
  (G.n,G.constant,List.ofFn (fun i => (work (labels.symm i),
    (G.left (labels.symm i)).val,(G.right (labels.symm i)).val,G.weight (labels.symm i))))

theorem erase_state (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m)
    (work : G.Edge → ℕ) : erase (state G labels work).2.2=QuantumListGraph.packed G labels := by
  simp only [erase,state,List.map_ofFn,QuantumListGraph.packed,Function.comp_def]

theorem valid (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m)
    (work : G.Edge → ℕ) : Valid (state G labels work) := by
  constructor
  · rw [erase_state]
    exact QuantumListGraph.packed_bounded G labels
  · rw [erase_state]
    exact QuantumListGraph.packed_noLoops G labels

def scheduleRelabel (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m)
    (work : G.Edge → ℕ) :
    QMAPathRelabeling (schedule (state G labels work) (valid G labels work)) ⟨G,work⟩ where
  vertex := Equiv.refl _
  edge := (finCongr (show (state G labels work).2.2.length = m from List.length_ofFn)).trans labels.symm
  left := by
    intro e
    apply Fin.ext
    simp only [schedule,graph,state,List.get_eq_getElem,List.getElem_ofFn]
    rfl
  right := by
    intro e
    apply Fin.ext
    simp only [schedule,graph,state,List.get_eq_getElem,List.getElem_ofFn]
    rfl
  work := by
    intro e
    change ((List.ofFn (fun i : Fin m => (work (labels.symm i),
      (G.left (labels.symm i)).val,(G.right (labels.symm i)).val,G.weight (labels.symm i)))).get e).1 = _
    exact (congrArg Prod.fst (List.get_ofFn
      (fun i : Fin m => (work (labels.symm i),
        (G.left (labels.symm i)).val,(G.right (labels.symm i)).val,G.weight (labels.symm i))) e))

end ContinuumCoulomb.QuantumPackedSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortScheduleActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed schedule has precisely the coefficients, work counts and
physical port paths of the proved spatial construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortScheduleActual
open QuantumForkList QuantumRouteCode

variable {rows width A D : ℕ} (I : SpatialInput rows width A D)
variable (hA : 0 < spatialDensity A D)

abbrev tape := QuantumForkGridProgram.output D (QuantumSpatialInputTape.input I)

end ContinuumCoulomb.QuantumPortScheduleActual

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

def inputCode : Input → List Bool := prodCode ratCode QuantumForkGridProgram.preparedCode

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

def inputCode : Input → List Bool := QuantumSpatialPortProgram.inputCode

end ContinuumCoulomb.QuantumSpatialCrossingProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvenRouteLabels
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

def selectedEquiv (G : QMARationalExchangeGraph) :
    Fin (Finset.univ : Finset G.Edge).card ≃ G.Edge where
  toFun := QMAEvenRouteData.selected
  invFun e := (Finset.univ : Finset G.Edge).equivFin ⟨e,Finset.mem_univ e⟩
  left_inv i := by
    change (Finset.univ : Finset G.Edge).equivFin
      ⟨((Finset.univ : Finset G.Edge).equivFin.symm i).val,_⟩=i
    exact (Finset.univ : Finset G.Edge).equivFin.apply_symm_apply i
  right_inv e := by
    change ((Finset.univ : Finset G.Edge).equivFin.symm
      ((Finset.univ : Finset G.Edge).equivFin ⟨e,Finset.mem_univ e⟩)).val=e
    rw [Equiv.symm_apply_apply]

def activeIndex : Fin m ≃ Fin (Finset.univ : Finset G.Edge).card :=
  labels.symm.trans (selectedEquiv G).symm

theorem selected_index (i : Fin m) :
    QMAEvenRouteData.selected (activeIndex labels i)=labels.symm i := by
  exact (selectedEquiv G).apply_symm_apply (labels.symm i)

def vertex : Fin (G.n+m*2) ≃ Fin (G.n+(Finset.univ : Finset G.Edge).card*2) :=
  ((vertexEquiv G.n m).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr (activeIndex labels) (Equiv.refl _)))).trans
      (vertexEquiv _ _)

@[simp] theorem vertex_old (v : Fin G.n) : vertex labels (old G.n m v)=old _ _ v := by
  simp only [vertex,old,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply,
    Sum.map_inl,Equiv.refl_apply]

@[simp] theorem vertex_fresh (i : Fin m) (a : Fin 2) :
    vertex labels (fresh G.n m i a)=fresh _ _ (activeIndex labels i) a := by
  simp only [vertex,fresh,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply,
    Sum.map_inr,Equiv.prodCongr_apply]
  rfl

def edge (t : Fin m × Fin 3) : QMAPartialPathsEdge (Finset.univ : Finset G.Edge) :=
  if h : t.2=0 then .inr (.inl (activeIndex labels t.1))
  else .inr (.inr (activeIndex labels t.1,⟨t.2.val-1,by omega⟩))

def unedge : QMAPartialPathsEdge (Finset.univ : Finset G.Edge) → Fin m × Fin 3
  | .inl e => (e.property (Finset.mem_univ _)).elim
  | .inr (.inl i) => ((activeIndex labels).symm i,0)
  | .inr (.inr (i,a)) => ((activeIndex labels).symm i,a.succ)

def edgeEquiv : (Fin m × Fin 3) ≃ QMAPartialPathsEdge (Finset.univ : Finset G.Edge) where
  toFun := edge labels
  invFun := unedge labels
  left_inv := by
    rintro ⟨i,k⟩
    fin_cases k
    all_goals
      change ((activeIndex labels).symm (activeIndex labels i),_)=(i,_)
      rw [Equiv.symm_apply_apply]
      rfl
  right_inv := by
    rintro (e | (i | ⟨i,a⟩))
    · exact (e.property (Finset.mem_univ _)).elim
    · change Sum.inr (Sum.inl (activeIndex labels ((activeIndex labels).symm i)))=Sum.inr (Sum.inl i)
      rw [Equiv.apply_symm_apply]
    · fin_cases a
      all_goals
        change Sum.inr (Sum.inr (activeIndex labels ((activeIndex labels).symm i),_))=Sum.inr (Sum.inr (i,_))
        rw [Equiv.apply_symm_apply]
        rfl

def work (t : Fin m × Fin 3) : ℕ := if t.2=2 then 4*P.length (labels.symm t.1)-1 else 0

theorem work_eq (t : Fin m × Fin 3) :
    P.toEven.nextWork (edge labels t)=work P labels t := by
  rcases t with ⟨i,k⟩
  fin_cases k
  · rfl
  · rfl
  · change 4*P.length (QMAEvenRouteData.selected (activeIndex labels i))-1=
      4*P.length (labels.symm i)-1
    rw [selected_index labels i]

end ContinuumCoulomb.QuantumEvenRouteLabels

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLatticeSerialization
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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
open MediatorListProgram

def inputCode : Input → List Bool :=
  prodCode (listCode coordinateCode) (prodCode (listCode bondCode) thresholdCode)

noncomputable def rationalProgram : Procedure ratCode binaryRationalCodec.encode BinaryRational.ofRat :=
  ((EncodingPrograms.appendPair BinaryEncoding.integer BinaryEncoding.natural).comp
    ((EncodingPrograms.integerOutput.comp Procedure.ratNum).pair
      (EncodingPrograms.naturalOutput.comp Procedure.ratDen))).result (by intro q; rfl)

noncomputable def coordinateProgram : Procedure coordinateCode SourcePrograms.coordinateCodec.encode id :=
  ((EncodingPrograms.appendPair BinaryEncoding.integer BinaryEncoding.integer).comp
    ((EncodingPrograms.integerOutput.comp (Procedure.first _ _)).pair
      (EncodingPrograms.integerOutput.comp (Procedure.second _ _)))).congrFun (by rintro ⟨x,y⟩; rfl)

noncomputable def edgeProgram : Procedure bondCode binaryHeisenbergEdgeCodec.encode edge := by
  let tail := Procedure.second Nat.bits (prodCode Nat.bits ratCode)
  let right := EncodingPrograms.naturalOutput.comp ((Procedure.first _ _).comp tail)
  let weight := rationalProgram.comp ((Procedure.second _ _).comp tail)
  let rest := (EncodingPrograms.appendPair BinaryEncoding.natural binaryRationalCodec).comp (right.pair weight)
  exact ((EncodingPrograms.appendPair BinaryEncoding.natural
    (BinaryEncoding.pair BinaryEncoding.natural binaryRationalCodec)).comp
      ((EncodingPrograms.naturalOutput.comp (Procedure.first _ _)).pair rest)).result (by intro b; rfl)

noncomputable def coordinatesProgram : Procedure inputCode SourcePrograms.coordinateListCodec.encode Prod.fst :=
  ((PrefixListPrograms.listOutput SourcePrograms.coordinateCodec (0,0)).comp
    ((Procedure.listMap (0,0) (0,0) coordinateProgram).comp
      (Procedure.first _ _))).congrFun (by intro x; simp)

noncomputable def bondsProgram : Procedure inputCode SourcePrograms.edgeListCodec.encode
    (fun x => x.2.1.map edge) :=
  (PrefixListPrograms.listOutput binaryHeisenbergEdgeCodec ⟨0,0,⟨0,1⟩⟩).comp
    ((Procedure.listMap (0,0,0) ⟨0,0,⟨0,1⟩⟩ edgeProgram).comp
      ((Procedure.first _ _).comp (Procedure.second _ _)))

noncomputable def thresholdsProgram : Procedure inputCode SourcePrograms.thresholdCodec.encode
    (fun x => ((value x).lower,(value x).upper)) := by
  let t : Procedure inputCode thresholdCode (fun x => x.2.2) :=
    (Procedure.second _ _).comp (Procedure.second _ _)
  let a := (Procedure.first _ _).comp t
  let b := (Procedure.first _ _).comp ((Procedure.second _ _).comp t)
  let c := (Procedure.second _ _).comp ((Procedure.second _ _).comp t)
  let lower := rationalProgram.comp (Procedure.ratSub.comp (a.pair c))
  let upper := rationalProgram.comp (Procedure.ratSub.comp (b.pair c))
  exact (EncodingPrograms.appendPair binaryRationalCodec binaryRationalCodec).comp (lower.pair upper)

noncomputable def program : Procedure inputCode binaryHeisenbergCodec.encode value := by
  let tail := (EncodingPrograms.appendPair SourcePrograms.edgeListCodec SourcePrograms.thresholdCodec).comp
    (bondsProgram.pair thresholdsProgram)
  exact ((EncodingPrograms.appendPair SourcePrograms.coordinateListCodec SourcePrograms.sourceTailCodec).comp
    (coordinatesProgram.pair tail)).result (by intro x; rfl)

end ContinuumCoulomb.QuantumLatticeSerialization

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLatticeEncoding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_left _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_right _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite source objects serialize to valid binary instances with canonical
rational coefficients and the same physical sites and thresholds. -/

namespace ContinuumCoulomb.SquareLatticeHeisenberg

theorem binary_getEdge (d : SquareLatticeHeisenberg) (i : Fin d.binary.edges.length) :
    d.binary.edges.get i = d.binaryEdge ⟨i.val,by simpa using i.isLt⟩ := by
  exact get_ofFn_value d.binaryEdge i.val (by simpa using i.isLt)

theorem binary_getCoordinate (d : SquareLatticeHeisenberg) (i : Fin d.vertices) :
    d.binary.coordinate.getD i.val (0,0) = d.coordinate i := by
  rw [List.getD_eq_get _ _ ⟨i.val,by rw [binary_vertices]; exact i.isLt⟩]
  simp only [binary,List.get_ofFn]
  rfl

theorem binary_valid (d : SquareLatticeHeisenberg) : d.binary.Valid := by
  constructor
  · simpa using d.vertices_pos
  · exact List.nodup_ofFn.mpr d.coordinate_injective
  · intro e
    rw [d.binary_getEdge e]
    simpa only [binaryEdge,binary_vertices] using
      And.intro (d.left ⟨e.val,by simpa using e.isLt⟩).isLt
        (d.right ⟨e.val,by simpa using e.isLt⟩).isLt
  · intro e
    rw [d.binary_getEdge e]
    exact (d.coefficient _).den_pos
  · intro e
    rw [d.binary_getEdge e]
    simp only [binaryEdge,d.binary_getCoordinate]
    exact d.adjacent _
  · intro e f hef
    rw [d.binary_getEdge e,d.binary_getEdge f]
    let e' : Fin d.edges := ⟨e.val,by simpa using e.isLt⟩
    let f' : Fin d.edges := ⟨f.val,by simpa using f.isLt⟩
    have hne : e' ≠ f' := by
      intro h
      apply hef
      have hv : e.val = f.val := congrArg (fun z : Fin d.edges => z.val) h
      exact Fin.ext hv
    have hs := d.edge_simple e' f' hne
    constructor
    · rintro ⟨hl,hr⟩
      exact hs.1 ⟨Fin.ext hl,Fin.ext hr⟩
    · rintro ⟨hl,hr⟩
      exact hs.2 ⟨Fin.ext hl,Fin.ext hr⟩
  · exact d.lower.den_pos
  · exact d.upper.den_pos
  · simpa only [binary,BinaryRational.value_ofRat] using d.gap_pos

end ContinuumCoulomb.SquareLatticeHeisenberg

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

def inputCode : Input → List Bool := prodCode (listCode pairCode)
  (prodCode (listCode bondCode) QuantumLatticeSerialization.thresholdCode)

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

noncomputable def latticePacketProgram :
    Procedure (prodCode stateCode (prodCode ratCode ratCode))
      QuantumListLattice.inputCode (fun x : State × (ℚ × ℚ) => latticePacket x.1 x.2.1 x.2.2) := by
  let s := Procedure.first stateCode (prodCode ratCode ratCode)
  let t := Procedure.second stateCode (prodCode ratCode ratCode)
  let data := (Procedure.first QuantumListSchedule.stateCode
    (prodCode (listCode pairCode) (listCode (listCode pairCode)))).comp s
  let spatial := (Procedure.second QuantumListSchedule.stateCode
    (prodCode (listCode pairCode) (listCode (listCode pairCode)))).comp s
  let ps := (Procedure.first (listCode pairCode) (listCode (listCode pairCode))).comp spatial
  let tail := (Procedure.second unaryCode (prodCode ratCode (listCode entryCode))).comp data
  let c := (Procedure.first ratCode (listCode entryCode)).comp tail
  let xs := eraseProgram.comp ((Procedure.second ratCode (listCode entryCode)).comp tail)
  let a := (Procedure.first ratCode ratCode).comp t
  let b := (Procedure.second ratCode ratCode).comp t
  exact ps.pair (xs.pair (a.pair (b.pair c)))

theorem represented_length (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs)) (hP : Represents s hs P) :
    s.2.1.length=s.1.1 := by rw [hP.1,List.length_ofFn]; rfl

theorem represented_bounded (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs)) (hP : Represents s hs P) :
    SourceBondLists.bounded s.2.1.length (erase s.1.2.2) := by
  rw [represented_length s hs P hP]
  exact hs.1

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

def inputCode : Input → List Bool := prodCode QuantumSpatialPortProgram.inputCode
  (prodCode ratCode ratCode)

noncomputable opaque spatialInputProgram : Procedure inputCode
    QuantumSpatialPortProgram.inputCode Prod.fst := Procedure.first _ _
noncomputable opaque thresholdsProgram : Procedure inputCode (prodCode ratCode ratCode) Prod.snd :=
  Procedure.second _ _
noncomputable opaque precisionProgram : Procedure inputCode ratCode (fun x => x.1.1) :=
  (Procedure.first ratCode QuantumForkGridProgram.preparedCode).comp spatialInputProgram

end ContinuumCoulomb.QuantumFinalRoutingProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvenTapeGeometry
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

def tagLeft (t : Fin m × Fin 3) : Fin (G.n+m*2) :=
  ![fresh G.n m t.1 0,old G.n m (G.left (labels.symm t.1)),
    old G.n m (G.right (labels.symm t.1))] t.2
def tagRight (t : Fin m × Fin 3) : Fin (G.n+m*2) :=
  ![fresh G.n m t.1 1,fresh G.n m t.1 0,fresh G.n m t.1 0] t.2

theorem fresh_val (i : Fin m) (a : Fin 2) :
    (fresh G.n m i a).val=G.n+2*i.val+a.val := by
  change G.n+(a.val+2*i.val)=_
  omega

theorem old_val (v : Fin G.n) : (old G.n m v).val=v.val := rfl

theorem tag_left (t : Fin m × Fin 3) :
    QuantumEvenRouteLabels.vertex labels (tagLeft labels t)=
      (P.toEven.schedule N).graph.left (QuantumEvenRouteLabels.edge labels t) := by
  rcases t with ⟨i,k⟩
  fin_cases k
  · exact QuantumEvenRouteLabels.vertex_fresh labels i 0
  · change QuantumEvenRouteLabels.vertex labels (old G.n m (G.left (labels.symm i)))=
      old _ _ (G.left (QMAEvenRouteData.selected (QuantumEvenRouteLabels.activeIndex labels i)))
    rw [QuantumEvenRouteLabels.selected_index,QuantumEvenRouteLabels.vertex_old]
  · change QuantumEvenRouteLabels.vertex labels (old G.n m (G.right (labels.symm i)))=
      old _ _ (G.right (QMAEvenRouteData.selected (QuantumEvenRouteLabels.activeIndex labels i)))
    rw [QuantumEvenRouteLabels.selected_index,QuantumEvenRouteLabels.vertex_old]

theorem tag_right (t : Fin m × Fin 3) :
    QuantumEvenRouteLabels.vertex labels (tagRight (G := G) t)=
      (P.toEven.schedule N).graph.right (QuantumEvenRouteLabels.edge labels t) := by
  rcases t with ⟨i,k⟩
  fin_cases k
  · exact QuantumEvenRouteLabels.vertex_fresh labels i 1
  · exact QuantumEvenRouteLabels.vertex_fresh labels i 0
  · exact QuantumEvenRouteLabels.vertex_fresh labels i 0

end ContinuumCoulomb.QuantumEvenTapeGeometry

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateEntryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact gate entries from a bounded register scan.  Work is unary, addresses
and support labels are binary, and each quantum bit is read from the supplied
small support table.  No sum over ambient configurations occurs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumGateEntryProgram
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumCircuitCode
open scoped Classical

noncomputable opaque queryProgram : Procedure pointCode QuantumHistoryBitProgram.queryCode
    (fun p => (p.1.2.1+p.2,p.1.2.2.2)) := by
  let x := Procedure.first inputCode Nat.bits
  let k := Procedure.second inputCode Nat.bits
  let tail := (Procedure.second unaryCode
    (prodCode Nat.bits (prodCode gateCode QuantumHistoryBitProgram.dataCode))).comp x
  let base := (Procedure.first Nat.bits
    (prodCode gateCode QuantumHistoryBitProgram.dataCode)).comp tail
  let rest := (Procedure.second Nat.bits
    (prodCode gateCode QuantumHistoryBitProgram.dataCode)).comp tail
  let d := (Procedure.second gateCode QuantumHistoryBitProgram.dataCode).comp rest
  exact (Procedure.binaryAdd.comp (base.pair k)).pair d

noncomputable opaque pointRowProgram : Procedure pointCode Nat.bits
    (fun p => (row p.1 p.2).val) := QuantumHistoryBitProgram.rowProgram.comp queryProgram

noncomputable opaque pointColumnProgram : Procedure pointCode Nat.bits
    (fun p => (column p.1 p.2).val) := QuantumHistoryBitProgram.columnProgram.comp queryProgram

noncomputable opaque pointProgram : Procedure pointCode Procedure.boolCode
    (fun p => point p.1 p.2) := by
  let x := Procedure.first inputCode Nat.bits
  let k := Procedure.second inputCode Nat.bits
  let l := leftProgram.comp x
  let r := rightProgram.comp x
  let s := pointRowProgram
  let t := pointColumnProgram
  let control := pointColumnProgram.comp (x.pair l)
  let one := Procedure.constant pointCode Nat.bits 1
  let tag := tagProgram.comp x
  let hit := Procedure.boolAnd.comp
    ((Procedure.binaryEq.comp (k.pair r)).pair (Procedure.binaryEq.comp (control.pair one)))
  let flipped := Procedure.binarySub.comp (one.pair t)
  let expected := Procedure.conditional hit flipped t
  let cnot := Procedure.binaryEq.comp (s.pair expected)
  let single := Procedure.boolOr.comp
    ((Procedure.binaryEq.comp (k.pair l)).pair (Procedure.binaryEq.comp (s.pair t)))
  exact (Procedure.conditional (Procedure.binaryEq.comp
    (tag.pair (Procedure.constant pointCode Nat.bits 2))) cnot single).congrFun (by
      intro p
      simp only [Function.comp_apply,point,decide_eq_true_eq,Bool.and_eq_true])

noncomputable opaque allWorkProgram : Procedure inputCode Procedure.boolCode allWork := by
  let testAt : Procedure (prodCode unaryCode inputCode) Procedure.boolCode
      (fun p => point p.2 p.1) :=
    pointProgram.comp ((Procedure.second unaryCode inputCode).pair
      (Procedure.unaryToBits.comp (Procedure.first unaryCode inputCode)))
  let count := Procedure.unarySuccessor.comp
    (Procedure.first unaryCode (prodCode Nat.bits
      (prodCode gateCode QuantumHistoryBitProgram.dataCode)))
  exact (QuantumHistoryBitProgram.allProgram.comp
    ((Procedure.tabulate (f := point) false testAt).comp
      (count.pair (Procedure.identity inputCode)))).congrFun (by intro x; rfl)

noncomputable opaque entryProgram : Procedure inputCode scalarCode entry := by
  let x := Procedure.identity inputCode
  let query := x.pair leftProgram
  let values := (pointRowProgram.comp query).pair (pointColumnProgram.comp query)
  let h := (QuantumHistoryBitProgram.matrixEntryProgram QuantumAlgebraicHistory.hadamard).comp values
  let t := (QuantumHistoryBitProgram.matrixEntryProgram QuantumAlgebraicHistory.phaseT).comp values
  let one := Procedure.constant inputCode scalarCode (rat 1)
  let zero := Procedure.constant inputCode scalarCode (rat 0)
  let isH := Procedure.binaryEq.comp (tagProgram.pair (Procedure.constant inputCode Nat.bits 0))
  let isT := Procedure.binaryEq.comp (tagProgram.pair (Procedure.constant inputCode Nat.bits 1))
  exact (Procedure.conditional allWorkProgram
    (Procedure.conditional isH h (Procedure.conditional isT t one)) zero).congrFun (by
      intro x
      simp only [Function.comp_apply,id_eq,entry,decide_eq_true_eq,QuantumHistoryBitProgram.matrixEntry]
      have hs : QuantumHistoryBitProgram.bit (row x (left x)).val=row x (left x) := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt (Fin.isLt _)
      have ht : QuantumHistoryBitProgram.bit (column x (left x)).val=column x (left x) := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt (Fin.isLt _)
      rw [hs,ht])

end ContinuumCoulomb.QuantumGateEntryProgram

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

noncomputable opaque pointProgram : Procedure pointCode Procedure.boolCode
    (fun p => point p.1 p.2) := by
  let x := Procedure.first inputCode Nat.bits
  let k := Procedure.second inputCode Nat.bits
  let label := Procedure.binaryAdd.comp ((baseProgram.comp x).pair k)
  let query := label.pair (dataProgram.comp x)
  let r := rowProgram.comp query
  let c := columnProgram.comp query
  let flip := Procedure.boolAnd.comp ((flipProgram.comp x).pair
    (Procedure.binaryEq.comp (label.pair (targetProgram.comp x))))
  let expected := Procedure.conditional flip
    (Procedure.binarySub.comp ((Procedure.constant pointCode Nat.bits 1).pair c)) c
  exact (Procedure.binaryEq.comp (r.pair expected)).congrFun (by
    intro p
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,point,decide_eq_true_eq,Bool.and_eq_true]
    split_ifs <;> simp only [Fin.ext_iff,swap_val])

noncomputable opaque unaryPointProgram :
    Procedure (prodCode unaryCode inputCode) Procedure.boolCode
      (fun x => point x.2 x.1) :=
  pointProgram.comp ((Procedure.second unaryCode inputCode).pair
    (Procedure.unaryToBits.comp (Procedure.first unaryCode inputCode)))

noncomputable opaque program : Procedure inputCode Procedure.boolCode value :=
  (allProgram.comp ((Procedure.tabulate (f := fun x i => point x i) false unaryPointProgram).comp
    (countProgram.pair (Procedure.identity inputCode)))).congrFun (by
      intro x
      simp only [Function.comp_apply,id_eq,value,allBits])

end ContinuumCoulomb.QuantumHistoryComparison

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

noncomputable opaque guardProgram : Procedure inputCode Procedure.boolCode
    (fun x : Input => guard x.1 x.2.1.2 x.2.2) := by
  let zero := Procedure.constant inputCode Nat.bits 0
  let one := Procedure.constant inputCode Nat.bits 1
  let two := Procedure.constant inputCode Nat.bits 2
  let left := Procedure.binaryEq.comp ((clockValueProgram indexProgram).pair one)
  let right := Procedure.binaryEq.comp
    ((clockValueProgram (Procedure.binaryAdd.comp (indexProgram.pair two))).pair zero)
  let middle := Procedure.binaryEq.comp
    ((clockValueProgram (Procedure.successor.comp indexProgram)).pair zero)
  exact (Procedure.boolAnd.comp (left.pair
    (Procedure.boolAnd.comp (right.pair middle)))).congrFun (by
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [guard,Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,
        Nat.succ_eq_add_one,Fin.ext_iff,Fin.val_one,Fin.val_zero])

noncomputable opaque flippedProgram : Procedure inputCode Procedure.boolCode
    (fun x : Input => flipped x.1 x.2.1.2 x.2.2) := by
  let target := Procedure.binaryAdd.comp
    (clockBaseProgram.pair (Procedure.successor.comp indexProgram))
  let args := allCountProgram.pair (clockBaseProgram.pair
    ((Procedure.constant inputCode Procedure.boolCode true).pair (target.pair dataProgram)))
  exact QuantumHistoryComparison.program.comp args

noncomputable opaque sameClockProgram : Procedure inputCode Procedure.boolCode
    (fun x : Input => sameClock x.1 x.2.2) :=
  QuantumHistoryComparison.program.comp
    (clockCountProgram.pair (clockBaseProgram.pair
      ((Procedure.constant inputCode Procedure.boolCode false).pair
        ((Procedure.constant inputCode Nat.bits 0).pair dataProgram))))

noncomputable opaque gateEntryProgram : Procedure inputCode scalarCode
    (fun x : Input => QuantumGateEntryProgram.entry
      (x.1.work,referenceWork x.1+1+(x.1.gates.length+2),
        QuantumHistorySiteProgram.gateAt (x.1,x.2.1.2),x.2.2)) :=
  QuantumGateEntryProgram.entryProgram.comp
    ((workProgram.comp circuitProgram).pair (workBaseProgram.pair
      ((QuantumHistorySiteProgram.gateAtProgram.comp
        (circuitProgram.pair indexProgram)).pair dataProgram)))

end ContinuumCoulomb.QuantumHistoryDelta

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

def inputCode : Input → List Bool :=
  prodCode unaryCode (prodCode (listCode Nat.bits) matrixCode)

noncomputable opaque precisionProgram : Procedure inputCode unaryCode Prod.fst := Procedure.first _ _
noncomputable opaque indicesProgram : Procedure inputCode (listCode Nat.bits) (fun x => x.2.1) :=
  (Procedure.first _ _).comp (Procedure.second _ _)
noncomputable opaque matrixProgram : Procedure inputCode matrixCode (fun x => x.2.2) :=
  (Procedure.second _ _).comp (Procedure.second _ _)

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationSupport
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

def sites (c : QMACircuit) (t : Fin c.gates.length) : List (QMACircuitQubit c) :=
  (propagationSites c t).dedup

theorem sites_nodup (c : QMACircuit) (t : Fin c.gates.length) :
    (sites c t).Nodup := List.nodup_dedup _

def labels (c : QMACircuit) (t : Fin c.gates.length) : List ℕ :=
  (sites c t).map (fun q => siteNumber c (.inr q))

def data (c : QMACircuit) (t : Fin c.gates.length)
    (s r : Fin (sites c t).length → Fin 2) : Data :=
  (labels c t,List.ofFn (fun i => (s i).val),List.ofFn (fun i => (r i).val))

end ContinuumCoulomb.QuantumPropagationSupport

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

noncomputable opaque cutoffProgram : Procedure inputCode Nat.bits
    (fun x => referenceWork x.1+1) :=
  Procedure.successor.comp (referenceWorkProgram.comp circuitProgram)

end ContinuumCoulomb.QuantumHistoryTableProgram

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

noncomputable opaque classifyProgram : Procedure (listCode entryCode)
    (listCode QuantumRawExchange.rawCode) classify := by
  let p := Procedure.listMap ([],0) QuantumRawExchange.zeroRaw QuantumOrderedRawPacking.program
  exact p.congrEncoding (by intro xs; rfl) (by intro ys; rfl)

end ContinuumCoulomb.QuantumOrderedLabelCompile

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

def outputEnergy (x : Input) : ℝ :=
  MediatorGraph.normalizedBottom (QuantumRawExchange.rawMatrix (qubitCount x) (output x))

end ContinuumCoulomb.QuantumOrderedLabelCompile

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

noncomputable opaque columnsProgram : Procedure (prodCode unaryCode Nat.bits)
    (listCode Nat.bits) (fun x => columns x.1 x.2) := by
  let width := Procedure.first unaryCode Nat.bits
  let context := (Procedure.unaryToBits.comp width).pair (Procedure.second unaryCode Nat.bits)
  let env := Procedure.second unaryCode pairCode
  let w := (Procedure.first Nat.bits Nat.bits).comp env
  let order := (Procedure.second Nat.bits Nat.bits).comp env
  let index := Procedure.unaryToBits.comp (Procedure.first unaryCode pairCode)
  let entry := sweepIndexProgram.comp (w.pair (order.pair index))
  exact ((Procedure.tabulate (f := fun x i => sweepIndex x.1 x.2 i) 0 entry).comp
    ((Procedure.unarySuccessor.comp width).pair context)).congrFun (by intro x; rfl)

noncomputable def takeProgram : Procedure (prodCode Nat.bits (listCode Nat.bits))
    (listCode Nat.bits) (fun x => x.2.take x.1) := by
  let n := Procedure.first Nat.bits (listCode Nat.bits)
  let xs := Procedure.second Nat.bits (listCode Nat.bits)
  let len := (Procedure.listLength Nat.bits 0).comp xs
  let count := Procedure.binarySub.comp (len.pair n)
  let rev := (Procedure.listReverse Nat.bits 0).comp xs
  exact ((Procedure.listReverse Nat.bits 0).comp
    ((Procedure.listDrop Nat.bits).comp (count.pair rev))).congrFun (by
      intro x
      simp only [Function.comp_apply,← List.reverse_take,List.reverse_reverse])

end ContinuumCoulomb.QuantumSweepCells

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

def finalInputCode : FinalInput → List Bool :=
  prodCode (prodCode ratCode QuantumForkGridProgram.preparedCode) (prodCode ratCode ratCode)

end ContinuumCoulomb.QuantumHistoryPreparedProgram

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

theorem inputCode_eq : QuantumHistoryPreparedProgram.finalInputCode=
    QuantumFinalRoutingProgram.inputCode := rfl

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
open QuantumCrossingSelectProgram
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (s : QuantumListSchedule.State) (hs : QuantumListSchedule.Valid s)
    (E : QMAPathRelabeling (QuantumListSchedule.schedule s hs) (P.schedule.iterate N D))
    {r : ℕ} (cell : Fin r ≃ Fin P.crossingCells.card)

def site (i : Fin r) (a : Fin 4) : Fin s.1 :=
  E.vertex.symm (P.crossingSiteFin N hD (cell i) a)

theorem site_global : Function.Injective (fun p : Fin r × Fin 4 => site P N hD s hs E cell p.1 p.2) :=
  QuantumCrossingSiteProgram.reordered_sites_global P N hD E.vertex cell

theorem site_injective (i : Fin r) : Function.Injective (site P N hD s hs E cell i) := by
  intro a b hab
  exact congrArg Prod.snd (site_global P N hD s hs E cell (a₁ := (i,a)) (a₂ := (i,b)) hab)

end ContinuumCoulomb.QuantumScheduleCrossingGeometry

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceGridGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scale and box identities for the existing source nuclear program.
The calibrated source-site geometry is handled separately. -/

noncomputable section
namespace ContinuumCoulomb.SourceNuclearProgram

def radii (k : ℕ) (d : BinaryHeisenberg) : CenteredGaussLabels.Radii :=
  (SourcePhysicalThreshold.horizontalRadius k d,
    (SourcePhysicalThreshold.horizontalRadius k d,SourcePhysicalThreshold.verticalRadius k d))

end ContinuumCoulomb.SourceNuclearProgram

end

end OAI
end


