-- Prove2me | Definitions.Def_OAIQ092A003
-- name    : OAIQ092A003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T19:45:44.558038+00:00
-- url     : https://prove2.me/theorems/73ffd8f7-5c25-48da-b5bb-15231fdc0ea4
-- title:
--   Definitions bundle OAIQ092A003 of the split of OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 420 declarations of OpenAI's Lean: 297 definitions, 2 inductive types or structures, 11 instances and 110 theorems. The definitions and types are `OAI.ContinuumCoulomb.configurationComplexLaplacian`, `OAI.ContinuumCoulomb.configurationComplexPartial`, `OAI.ContinuumCoulomb.configurationRealLaplacian`, `OAI.ContinuumCoulomb.configurationRealPartial`, `OAI.ContinuumCoulomb.contactGridAxis`, `OAI.ContinuumCoulomb.contactHeightHigh`, `OAI.ContinuumCoulomb.contactHeightLow`, `OAI.ContinuumCoulomb.contactLengthTolerance`, `OAI.ContinuumCoulomb.coordinateProduct`, `OAI.ContinuumCoulomb.coreOrbitalCoefficient`, `OAI.ContinuumCoulomb.coulombLineKernel`, `OAI.ContinuumCoulomb.coulombNumericalBox`, `OAI.ContinuumCoulomb.cubePoint`, `OAI.ContinuumCoulomb.dilateState`, `OAI.ContinuumCoulomb.dilatedNuclei`, `OAI.ContinuumCoulomb.directionalSecond`, `OAI.ContinuumCoulomb.electronBall`, `OAI.ContinuumCoulomb.electronSlotKinetic`, `OAI.ContinuumCoulomb.finiteFourIndexChange`, `OAI.ContinuumCoulomb.finiteTensorResidualValue`, `OAI.ContinuumCoulomb.finiteTwoIndexChange`, `OAI.ContinuumCoulomb.flatCoulombTensor`, `OAI.ContinuumCoulomb.flatNuclearMatrix`, `OAI.ContinuumCoulomb.flatPairCoulomb`, `OAI.ContinuumCoulomb.flatResidualMatrix`, `OAI.ContinuumCoulomb.flowCoordinate`, `OAI.ContinuumCoulomb.flowMatrix`, `OAI.ContinuumCoulomb.formGroundEnergy`, `OAI.ContinuumCoulomb.gaussCellCenter`, `OAI.ContinuumCoulomb.gaussNodeTriple`, `OAI.ContinuumCoulomb.gaussianLineEquiv`, `OAI.ContinuumCoulomb.gaussianPotential`, `OAI.ContinuumCoulomb.heisenberg`, `OAI.ContinuumCoulomb.hydrogenEnergy`, `OAI.ContinuumCoulomb.hydrogenForm`, `OAI.ContinuumCoulomb.inverseFifthRadial`, `OAI.ContinuumCoulomb.inverseFifthTail`, `OAI.ContinuumCoulomb.lastTensorFiber`, `OAI.ContinuumCoulomb.mediatorMemberSign`, `OAI.ContinuumCoulomb.normalizedDilation` and 259 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/Computability, lean/OAI/MathematicalPhysics, in whole or in part: `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Approximation`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_ArzelaAscoli`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Compactness`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Kernels`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Transfer`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_TranslationIntegral`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimate`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1`, `BiholderTransport_Calculus_PathCalculus`, `ContinuumCoulomb_ManyBody_ElectronSlotBound`, `ContinuumCoulomb_ManyBody_FiniteCoefficientCorrection`, `ContinuumCoulomb_ManyBody_FiniteOrbitalLaplacian`, `ContinuumCoulomb_ManyBody_FiniteTensorFormCompression`, `ContinuumCoulomb_ManyBody_FiniteTensorFormError`, `ContinuumCoulomb_ManyBody_FiniteTensorResidual`, `ContinuumCoulomb_ManyBody_MediatorEffective`, `ContinuumCoulomb_ManyBody_PairSpinOrbitals`, `ContinuumCoulomb_ManyBody_PairTensorCompression`, `ContinuumCoulomb_ManyBody_RepulsionBound`, `ContinuumCoulomb_ManyBody_Singlet`, `ContinuumCoulomb_ManyBody_Spin`, `ContinuumCoulomb_ManyBody_TensorDifferential`, `ContinuumCoulomb_ManyBody_TensorFirstReplacement`, `ContinuumCoulomb_ManyBody_TensorOperatorResidual`, `ContinuumCoulomb_ManyBody_TensorSlotReplacement`, `ContinuumCoulomb_ManyBody_TensorTotalReplacement`, `ContinuumCoulomb_ManyBody_WeightedNuclearCross`, `ContinuumCoulomb_ManyBody_WeightedNuclearForm`, `ContinuumCoulomb_Nuclei_FlowMatrix`, `ContinuumCoulomb_Nuclei_GaussEightNodes`, `ContinuumCoulomb_Nuclei_GaussLocal`, `ContinuumCoulomb_Nuclei_GaussPositionCell`, `ContinuumCoulomb_Nuclei_NuclearCutoff`, `ContinuumCoulomb_Nuclei_NuclearNearEstimate`, `ContinuumCoulomb_Nuclei_SlabLineIntegral`, `ContinuumCoulomb_Nuclei_SlabPlanarIntegral`, `ContinuumCoulomb_Nuclei_SlabPlanarTail`, `ContinuumCoulomb_Nuclei_SlabProfile`, `ContinuumCoulomb_Nuclei_SlabSections`, `ContinuumCoulomb_Nuclei_SlabVerticalCoordinates`, `ContinuumCoulomb_OneParticle_ComplexFormSplit`, `ContinuumCoulomb_OneParticle_ComplexMollification`, `ContinuumCoulomb_OneParticle_ContactAdjustment`, `ContinuumCoulomb_OneParticle_ContactExtent`, `ContinuumCoulomb_OneParticle_CoordinateLaplacian`, `ContinuumCoulomb_OneParticle_CoreOrbitalProjection`, `ContinuumCoulomb_OneParticle_CoreTensorFiber`, `ContinuumCoulomb_OneParticle_CoulombCubeCoordinates`, `ContinuumCoulomb_OneParticle_CoulombInverseFifth`, `ContinuumCoulomb_OneParticle_CubeGeometry`, `ContinuumCoulomb_OneParticle_GaussianJetBounds`, `ContinuumCoulomb_OneParticle_GaussianLine`, `ContinuumCoulomb_OneParticle_GaussianPoincare`, `ContinuumCoulomb_OneParticle_IsolatedForms`, `ContinuumCoulomb_OneParticle_IsolatedSpectrum`, `ContinuumCoulomb_OneParticle_LocalizedCoulombBox`, `ContinuumCoulomb_OneParticle_ManufacturedFrequency`, `ContinuumCoulomb_OneParticle_OneElectronClosure`, `ContinuumCoulomb_OneParticle_OneElectronCoordinates`, `ContinuumCoulomb_OneParticle_OneElectronTrial`, `ContinuumCoulomb_OneParticle_OrbitalGraphBounds`, `ContinuumCoulomb_OneParticle_PlanarExponentialEnvelope`, `ContinuumCoulomb_OneParticle_RealOneElectronState`, `ContinuumCoulomb_OneParticle_RealOrbitalResidual`, `ContinuumCoulomb_OneParticle_RealSpinOrbitals`, `ContinuumCoulomb_OneParticle_ScalarMollification`, `ContinuumCoulomb_OneParticle_SmoothCutoffApproximation`, `ContinuumCoulomb_OneParticle_SplitPullback`, `ContinuumCoulomb_OneParticle_VerticalCappedForm`, `ContinuumCoulomb_OneParticle_VerticalCutoffTail`, `ContinuumCoulomb_OneParticle_WeakComplexLaplacian`, `ContinuumCoulomb_OneParticle_WeakH1Laplacian`, `ContinuumCoulomb_Quantum_QuantumAncilla`, `ContinuumCoulomb_Quantum_QuantumAncillaCompression`, `ContinuumCoulomb_Quantum_QuantumBlockEdges`, `ContinuumCoulomb_Quantum_QuantumCrossingBounds`, `ContinuumCoulomb_Quantum_QuantumCrossingEffective`, `ContinuumCoulomb_Quantum_QuantumCrossingsGraph`, `ContinuumCoulomb_Quantum_QuantumForkBounds`, `ContinuumCoulomb_Quantum_QuantumForkEffective`, `ContinuumCoulomb_Quantum_QuantumForkGraph`, `ContinuumCoulomb_Quantum_QuantumForkInitialMatrix`, `ContinuumCoulomb_Quantum_QuantumFourAxis`, `ContinuumCoulomb_Quantum_QuantumFourBasis`, `ContinuumCoulomb_Quantum_QuantumFourCorrelation`, `ContinuumCoulomb_Quantum_QuantumFourCorrelationCertificate`, `ContinuumCoulomb_Quantum_QuantumFourCounterterm`, `ContinuumCoulomb_Quantum_QuantumFourCouplingScale`, `ContinuumCoulomb_Quantum_QuantumFourEffective`, `ContinuumCoulomb_Quantum_QuantumFourEncoding`, `ContinuumCoulomb_Quantum_QuantumFourGapCertificate`, `ContinuumCoulomb_Quantum_QuantumFourIsometry`, `ContinuumCoulomb_Quantum_QuantumFourLogical`, `ContinuumCoulomb_Quantum_QuantumFourPositive`, `ContinuumCoulomb_Quantum_QuantumFourSpinTable`, `ContinuumCoulomb_Quantum_QuantumFourStencils`, `ContinuumCoulomb_Quantum_QuantumFourTensorEffectiveError`, `ContinuumCoulomb_Quantum_QuantumFourTensorFullFamily`, `ContinuumCoulomb_Quantum_QuantumFourTensorOnsite`, `ContinuumCoulomb_Quantum_QuantumFourWeighted`, `ContinuumCoulomb_Quantum_QuantumGadgetCounterterms`, `ContinuumCoulomb_Quantum_QuantumPaddedBasis`, `ContinuumCoulomb_Quantum_QuantumPaddedInput`, `ContinuumCoulomb_Quantum_QuantumPathSubdivision`, `ContinuumCoulomb_Quantum_QuantumPathsGraph`, `ContinuumCoulomb_Quantum_QuantumPauliParity`, `ContinuumCoulomb_Quantum_QuantumPauliProduct`, `ContinuumCoulomb_Quantum_QuantumQuadratic`, `ContinuumCoulomb_Quantum_QuantumRationalDegreeReduction`, `ContinuumCoulomb_Quantum_QuantumRectangularOperator`, `ContinuumCoulomb_Quantum_QuantumRoutingScale`, `ContinuumCoulomb_Quantum_QuantumSpatialReindex`, `ContinuumCoulomb_Quantum_QuantumTensorSucc`, `ContinuumCoulomb_Quantum_QuantumThirdCounterterm`, `ContinuumCoulomb_Quantum_QuantumTransferSweep`, `ContinuumCoulomb_Quantum_QuantumWireGrid`, `ContinuumCoulomb_Quantum_QuantumXZSubdivision`, `ContinuumCoulomb_Quantum_QubitMediatorAncilla`, `ContinuumCoulomb_Quantum_QubitMediatorForms`, `ContinuumCoulomb_Quantum_QubitMediatorHilbert`, `ContinuumCoulomb_Quantum_QubitMediatorMatrix`, `ContinuumCoulomb_Quantum_QubitMediatorPenalty`, `ContinuumCoulomb_Quantum_QubitMediatorPhysical`, `ContinuumCoulomb_Quantum_QubitMediatorProjection`, `ContinuumCoulomb_Quantum_QubitMediatorSeriesMatrix`, `ContinuumCoulomb_Quantum_QubitPhase`, `ContinuumCoulomb_Quantum_QubitPhaseLocal`, `ContinuumCoulomb_Quantum_QubitPhasePhysical`, `ContinuumCoulomb_Quantum_QubitSubdivisionMatrix`, `ContinuumCoulomb_Quantum_QubitThirdFamilyBounds`, `ContinuumCoulomb_Quantum_QubitThirdNormBudget`, `ContinuumCoulomb_Reduction_Dilation`, `ContinuumCoulomb_Reduction_FormStability`, `ContinuumCoulomb_Reduction_LastTensorFiber`, `CoulombRadii_FieldAnalysis_BlockIndex`, `CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv`, `CoulombRadii_FieldAnalysis_CorePerm`, `CoulombRadii_FieldAnalysis_FermionicCoefficients`, `CoulombRadii_FieldAnalysis_Gaussian`, `CoulombRadii_FieldAnalysis_PairRegroup`, `CoulombRadii_FieldAnalysis_PermOrCompSwapOffTwo`, `CoulombRadii_FieldAnalysis_Space`, `CoulombRadii_FieldAnalysis_SpinCubeEquiv`, `CoulombRadii_FieldAnalysis_TsumFixed`, `CoulombRadii_FormDomain_Add`, `CoulombRadii_FormDomain_CoreKinetic`, `CoulombRadii_FormDomain_CoreSliceRegular`, `CoulombRadii_FormDomain_HardyMollifier`, `CoulombRadii_FormDomain_OrbitalHilbertBasis`, `CoulombRadii_FormDomain_Pullback`, `CoulombRadii_FormDomain_RegularizedHardyField`, `CoulombRadii_FormDomain_SmoothCompact`, `CoulombRadii_FormDomain_Translate`, `CoulombRadii_Localization_TruncatedCoulomb`, `CoulombRadii_Packets_CoulombKernel`, `CoulombRadii_Propagation_NuclearPotential`, `CoulombRadii_ThomasFermi_FirstFiber`, `KLS_Measures_PotentialMeasure`, `KLS_Model`, `KLS_Regularization_RegularPotential`, `KLS_Spectral_BrascampLiebMoments`, `KLS_Spectral_BrascampLiebPerturbation`, `KLS_Stein_SteinHessianDefs`, `Laughlin_Operators_NormalOrder`, `MinUncut_Search_RawRationalArithmetic`.
--
--   **Imports.** It imports the published bundle `Def_ContinuumCoulombHardness`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ092A007`, `OAIQ092A011` and `OAIQ092A012`; the statements `OAI.ContinuumCoulomb.ContactCalibratedGeometry.separation` and `OAI.ContinuumCoulomb.qmaXZSubdivision_accuracy`.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis, lean/OAI/Computability, lean/OAI/MathematicalPhysics at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
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
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Size
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
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
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
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Tilted
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
import Mathlib.Topology.Compactness.Compact
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

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
end OAICompat434

end OAI
end

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

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma tsupport_indicator_subset_closure (s : Set E) (f : E → ℝ) :
    tsupport (s.indicator f) ⊆ closure s := by
  -- `Function.support (s.indicator f) ⊆ s`, hence the topological support is contained in
  -- `closure s`.
  simpa [tsupport] using closure_mono (Set.support_indicator_subset (s := s) (f := f))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma hasCompactSupport_indicator_of_isCompact (s : Set E) (hs : IsCompact s) (f : E → ℝ) :
    HasCompactSupport (s.indicator f) := by
  have hs_closed : IsClosed s := hs.isClosed
  -- `tsupport (s.indicator f)` is closed and contained in the compact set `s`.
  refine hs.of_isClosed_subset (isClosed_tsupport _) ?_
  have : tsupport (s.indicator f) ⊆ closure s := tsupport_indicator_subset_closure (E := E) s f
  simpa [hs_closed.closure_eq] using this

end

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation
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
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Translation`

Translation utilities for the Euclidean Sobolev model spaces.

This file is intentionally “pre-Rellich”: it provides the algebraic/measure-theoretic translation
operators and their interaction with the `C¹_c` graph embedding used to define `H¹`.

## Main results

- `translateC1c`: translation as a linear endomorphism of `C¹_c`.
- `translateL2`: translation as a linear isometry of `L²` (under an invariant measure).
- `translateL2_toL2` / `translateL2_toL2Grad`: translation commutes with `toL2` / `toL2Grad`.
- `grad_translate`: the Euclidean gradient commutes with translation.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory

section Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance instMeasurableSpaceE_SobolevEuclideanTranslation : MeasurableSpace E := borel E
local instance instBorelSpaceE_SobolevEuclideanTranslation : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_SobolevEuclideanTranslation_rb5eb97_1 : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableAddE_SobolevEuclideanTranslation : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

variable (μ : Measure E) [μ.IsAddRightInvariant]

/-- Translation on `L²` as a linear isometry, under an additive right-invariant measure. -/
noncomputable def translateL2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E) :
    (E →₂[μ] F) →ₗᵢ[ℝ] (E →₂[μ] F) := by
  classical
  simpa using
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := F) (p := (2 : ENNReal))
      (μ := μ) (μb := μ) (f := fun x : E => x + a) (MeasureTheory.measurePreserving_add_right μ a))

end Measure

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Approximation
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
# `L²` compactness criterion: approximation-by-translation bounds (Euclidean)

This file will prove the key inequality used in the Fréchet–Kolmogorov approach: smoothing by a
probability kernel controls the `L²` error by the translation modulus.

## Main results (planned)

The principal statement will control `‖smoothL2 ψ u - extendByZeroL2 u‖₂` by an average (or sup) of
`‖translateL2 t (extendByZeroL2 u) - extendByZeroL2 u‖₂` over `t` in the support of `ψ`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpace_solutions_2 : MeasurableSpace E := borel E
local instance instBorelSpace_solutions_2 : BorelSpace E := ⟨rfl⟩

local instance instOpensMeasurableSpace_solutions_2_rb5eb97_1 : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableAdd_solutions_2_rb5eb97_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNeg_solutions_rb5eb97_1 : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
variable {K : Set E} (hK : IsCompact K) (hKm : MeasurableSet K)
variable (ψ : E → ℝ)

/-- The measure with density `ψ` with respect to Lebesgue measure. This will be a probability
measure once `ψ ≥ 0` and `∫ ψ = 1`. -/
noncomputable def kernelMeasure : Measure E :=
  (volume : Measure E).withDensity fun x => ENNReal.ofReal (ψ x)


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

local instance instMeasurableSpaceE_L2CompactnessCompactness : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessCompactness : BorelSpace E := ⟨rfl⟩

variable {K : Set E}
variable {ψ : E → ℝ}

/-- The natural compact codomain for smoothing on `K` by a compactly supported kernel `ψ`. -/
def Kψ : Set E :=
  K + tsupport ψ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma isCompact_Kψ (hK : IsCompact K) (hψcs : HasCompactSupport ψ) :
    IsCompact (Kψ (K := K) (ψ := ψ)) :=
  IsCompact.add hK hψcs.isCompact

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
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_ArzelaAscoli
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
# `L²` compactness criterion: Arzelà–Ascoli for the smoothing operator (Euclidean)

This file proves the Arzelà–Ascoli step for the compact smoothing operator used in the
Fréchet–Kolmogorov / Riesz–Kolmogorov approach to Euclidean Rellich–Kondrachov.

## Main result

- `smoothBCF_image_closedBall_isCompact`:
  For a compact set `K` and a continuous compactly supported kernel `ψ`, the family
  `{ smoothFun ψ u | ‖u‖ ≤ R }` restricted to the compact set `K + tsupport ψ`
  has compact closure in `BoundedContinuousFunction`.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.1.1`.
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

local instance instMeasurableSpaceE_L2CompactnessArzelaAscoli : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessArzelaAscoli : BorelSpace E := ⟨rfl⟩

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
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Transfer
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
# `L²` compactness criterion: transfer from `BCF` compactness to `L²` (Euclidean)

This file transfers the Arzelà–Ascoli compactness of the `BoundedContinuousFunction` packaging of
`smoothFun` on the compact set `K + tsupport ψ` to a compactness statement in `L²(volume)`.

## Main results

- `smoothL2_image_closedBall_isCompact`:
  For a compact set `K` and a continuous compactly supported kernel `ψ`, the family
  `{ smoothL2 ψ u | ‖u‖ ≤ R }` has compact closure in `L²(volume)`.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.1.2`.
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

local instance instMeasurableSpaceE_L2CompactnessTransfer : MeasurableSpace E := borel E

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
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov
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
# `L²` compactness criterion: Fréchet–Kolmogorov (Euclidean, compact support case)

This file packages the final “precompactness via smoothing” step behind the Euclidean `L²`
compactness criterion used by the Rellich–Kondrachov stack:

- the **smoothing operator** `smoothL2 ψ` has compact image on `Metric.closedBall 0 R`;
- the **approximation inequality** bounds `‖smoothL2 ψ u - extendByZeroL2 u‖` by a translation
  error.

We state the criterion at the level needed by the project: families of `L²` functions with common
compact support (modeled as `Lp ℝ 2 (volume.restrict K)` and embedded into `L²(volume)` via
`extendByZeroL2`).

## Main results

- `norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le`:
  if the translation error averaged against `kernelMeasure ψ` is ≤ `η²`, then smoothing approximates
  `extendByZeroL2` within `η`.
- `totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small`:
  if a bounded family admits, at every scale `ε`, a kernel `ψ` for which the above translation error
  is uniformly small, then the embedded family is totally bounded in `L²(volume)`.
- `isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small`:
  the corresponding compact-closure statement.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.3`.
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

local instance instMeasurableSpaceE_L2CompactnessFrechetKolmogorov : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessFrechetKolmogorov : BorelSpace E := ⟨rfl⟩

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
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Kernels
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
# `L²` compactness criterion: existence of small-support probability kernels (Euclidean)

This file provides a “kernel factory” for the Euclidean Fréchet–Kolmogorov / Riesz–Kolmogorov
criterion: for any radius `δ > 0`, produce a continuous compactly supported function `ψ : E → ℝ`
such that:

- `ψ ≥ 0`,
- `tsupport ψ ⊆ Metric.ball 0 δ`,
- `∫ ψ = 1` (so `kernelMeasure ψ` is a probability measure).

The construction uses mathlib’s `exists_smooth_tsupport_subset` bump-function lemma and normalizes
by its (positive) integral.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.5`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceE_L2CompactnessKernels : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessKernels : BorelSpace E := ⟨rfl⟩

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
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_TranslationIntegral
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
# `L²` compactness criterion: bounding the translation-integral by a translation modulus

This file provides a small but crucial bridge lemma used to connect a uniform translation modulus
on `L²(volume)` with the `kernelMeasure` translation-integral bound appearing in the
approximation-identity estimate.

The core observation is that if `ψ` is supported in a neighborhood where the translation modulus is
≤ `η`, then the averaged squared translation error against the probability measure
`kernelMeasure ψ` is ≤ `η²`.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.4`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceE_L2CompactnessTranslationIntegral : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessTranslationIntegral : BorelSpace E := ⟨rfl⟩

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
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimate
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
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimate`

Pointwise translation estimates for `C¹_c` functions on Euclidean spaces.

This file provides the key analytic inequality used later in the Euclidean Rellich step:
translation differences are controlled by the `L²`-gradient.

At this stage we only prove *pointwise* inequalities along the segment `t ↦ x + t • a`.
The measure-theoretic lifting to `L²` is tracked separately under `lean-103.5.2.26.5.3.2.3`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance instMeasurableSpaceE_SobolevEuclideanTranslationEstimate :
    MeasurableSpace E := borel E

/-! ## Derivative along a translated line -/

/-- The affine line `t ↦ x + t • a`. -/
def line (x a : E) (t : ℝ) : E :=
  x + t • a

/-! ## Pointwise translation bound via the gradient -/

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ092_CC.Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1
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
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateH1`

Extend Euclidean `L²` translation estimates from `C¹_c` to the closure-based Euclidean `H¹` space.

## Main results

- `norm_translateL2_sub_h1ToL2_le`: for `u ∈ H¹`, `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂`, where `∇u` is the
  `L²(E)` component in our `H¹ ⊆ L² × L²(E)` model.
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

local instance instMeasurableSpaceE_SobolevEuclideanTranslationEstimateH1 :
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
-- module Solutions.OAIQ092_CC.BiholderTransport_Calculus_PathCalculus
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

namespace WeakMTWTransport
universe u w
variable {K : Type w} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance pathCalculusNormedAddCommGroupContinuousLinearMap :
    NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance pathCalculusNormedSpaceContinuousLinearMap :
    NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
local instance pathCalculusNormedAddCommGroupContinuousMap :
    NormedAddCommGroup C(K,E →L[ℝ] F) := ContinuousMap.instNormedAddCommGroup

def pathLinearApply (A : C(K,E →L[ℝ] F)) : C(K,E) →L[ℝ] C(K,F) := by
  let L : C(K,E) →ₗ[ℝ] C(K,F) :=
    { toFun := fun u => ⟨fun t => A t (u t),A.continuous.clm_apply u.continuous⟩
      map_add' := by intro u v; ext t; exact map_add (A t) (u t) (v t)
      map_smul' := by intro c u; ext t; exact map_smul (A t) c (u t) }
  exact L.mkContinuous ‖A‖ (by
      intro u
      change ‖(⟨fun t => A t (u t),A.continuous.clm_apply u.continuous⟩ : C(K,F))‖ ≤ ‖A‖ * ‖u‖
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
      intro t
      exact (A t).le_opNorm (u t) |>.trans
        (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t)
          (norm_nonneg _) (norm_nonneg _)))

@[simp] lemma pathLinearApply_apply (A : C(K,E →L[ℝ] F)) (u : C(K,E)) (t : K) :
    pathLinearApply A u t = A t (u t) := rfl

lemma norm_pathLinearApply_le (A : C(K,E →L[ℝ] F)) : ‖pathLinearApply A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro u
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
  intro t
  exact (A t).le_opNorm (u t) |>.trans
    (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t)
      (norm_nonneg _) (norm_nonneg _))

def pathLinearApplyL : C(K,E →L[ℝ] F) →L[ℝ] C(K,E) →L[ℝ] C(K,F) := by
  let L : C(K,E →L[ℝ] F) →ₗ[ℝ] C(K,E) →L[ℝ] C(K,F) :=
    { toFun := fun (A : C(K,E →L[ℝ] F)) => pathLinearApply A
      map_add' := by intro A B; ext u t; rfl
      map_smul' := by intro c A; ext u t; rfl }
  refine LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := C(K,E →L[ℝ] F)) (F := C(K,E) →L[ℝ] C(K,F)) L 1 ?_
  intro A
  change ‖pathLinearApply A‖ ≤ 1 * ‖A‖
  simpa only [one_mul] using norm_pathLinearApply_le A

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_Space
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

noncomputable def totalCharge {M : ℕ} (S : Nuclei M) : ℝ := ∑ j, S.charge j

theorem memLp_two_real_mul {n : ℕ} {u : Configuration n → ℂ}
    (hu : MemLp u 2 volume) {f : Configuration n → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    MemLp (fun x => (f x : ℂ) * u x) 2 volume := by
  apply hu.of_le_mul (c := B) ((Complex.continuous_ofReal.comp hf).aestronglyMeasurable.mul
    hu.aestronglyMeasurable)
  filter_upwards [] with x
  simpa only [Pi.mul_apply, Function.comp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right (hB x) (norm_nonneg (u x))

noncomputable def H1Vector.smoothMul {n : ℕ} (ψ : H1Vector n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B D : ℝ) (hB : ∀ x, |f x| ≤ B)
    (hD : ∀ a x, |fderiv ℝ f x (EuclideanSpace.single a 1)| ≤ D) : H1Vector n where
  value s x := (f x : ℂ) * ψ.value s x
  gradient s a x :=
    (fderiv ℝ f x (EuclideanSpace.single a 1) : ℂ) * ψ.value s x +
      (f x : ℂ) * ψ.gradient s a x
  value_L2 s := memLp_two_real_mul (ψ.value_L2 s) hf.continuous hB
  partial_L2 s a :=
    (memLp_two_real_mul (ψ.value_L2 s)
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const) (hD a)).add
      (memLp_two_real_mul (ψ.partial_L2 s a) hf.continuous hB)
  weak_partial s a φ hφ hφc := by
    let v := EuclideanSpace.single a (1 : ℝ)
    have hφL : MemLp (fun x => (φ x : ℂ)) 2 volume :=
      (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
        (hφc.comp_left (by simp))
    have hdφL : MemLp (fun x => (fderiv ℝ φ x v : ℂ)) 2 volume :=
      (Complex.continuous_ofReal.comp
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
        ((hφc.fderiv_apply ℝ v).comp_left (by simp))
    have hA : Integrable (fun x => ((f x : ℂ) * ψ.value s x) *
        (fderiv ℝ φ x v : ℂ)) volume :=
      (memLp_two_real_mul (ψ.value_L2 s) hf.continuous hB).integrable_mul hdφL
    have hB' : Integrable (fun x =>
        ((fderiv ℝ f x v : ℂ) * ψ.value s x) * (φ x : ℂ)) volume :=
      (memLp_two_real_mul (ψ.value_L2 s)
        ((hf.continuous_fderiv (by simp)).clm_apply continuous_const) (hD a)).integrable_mul hφL
    have hC : Integrable (fun x => ((f x : ℂ) * ψ.gradient s a x) *
        (φ x : ℂ)) volume :=
      (memLp_two_real_mul (ψ.partial_L2 s a) hf.continuous hB).integrable_mul hφL
    have hweak := ψ.weak_partial s a (f * φ) (hf.mul hφ) hφc.mul_left
    have hprod : ∀ x, ψ.value s x * (fderiv ℝ (f * φ) x v : ℂ) =
        ((f x : ℂ) * ψ.value s x) * (fderiv ℝ φ x v : ℂ) +
        ((fderiv ℝ f x v : ℂ) * ψ.value s x) * (φ x : ℂ) := by
      intro x
      rw [fderiv_mul (hf.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
      simp only [add_apply, smul_apply,
        smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul]
      ring
    change (∫ x, ψ.value s x * (fderiv ℝ (f * φ) x v : ℂ)) = _ at hweak
    simp_rw [hprod] at hweak
    rw [integral_add hA hB'] at hweak
    have hr : ∀ x, ψ.gradient s a x * ((f * φ) x : ℂ) =
        ((f x : ℂ) * ψ.gradient s a x) * (φ x : ℂ) := by
      intro x
      simp only [Pi.mul_apply, Complex.ofReal_mul]
      ring
    simp_rw [hr] at hweak
    change (∫ x, ((f x : ℂ) * ψ.value s x) * (fderiv ℝ φ x v : ℂ)) = _
    simp_rw [add_mul]
    rw [integral_add hB' hC]
    linear_combination hweak

open ContinuousLinearMap
open scoped Convolution

structure HardyCoordinates (n : ℕ) (i : Fin n) where
  coord : Fin 3 → Configuration n → ℝ
  smooth : ∀ b, ContDiff ℝ (⊤ : ℕ∞) (coord b)
  directional : ∀ a b x, fderiv ℝ (coord a) x (EuclideanSpace.single (i,b) 1) =
    if a = b then 1 else 0

noncomputable def blockRadiusSq {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (x : Configuration n) : ℝ := ∑ b : Fin 3, (R.coord b x)^2

lemma blockRadiusSq_nonneg {n : ℕ} (i : Fin n) (R : HardyCoordinates n i) (x : Configuration n) :
    0 ≤ blockRadiusSq i R x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma contDiff_blockRadiusSq {n : ℕ} (i : Fin n) (R : HardyCoordinates n i) :
    ContDiff ℝ (⊤ : ℕ∞) (blockRadiusSq i R) := by
  apply ContDiff.sum
  intro b _
  exact (R.smooth b).pow 2

lemma fderiv_blockRadiusSq {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (x : Configuration n) (b : Fin 3) :
    fderiv ℝ (blockRadiusSq i R) x (EuclideanSpace.single (i,b) 1) =
      2 * R.coord b x := by
  unfold blockRadiusSq
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun a (y : Configuration n) => (R.coord a y)^2)
    (fun a _ => ((R.smooth a).differentiable (by simp) x).pow 2)]
  simp only [sum_apply]
  have heach : ∀ a : Fin 3,
      fderiv ℝ (fun y : Configuration n => (R.coord a y)^2) x
        (EuclideanSpace.single (i,b) 1) =
          if a = b then 2 * R.coord b x else 0 := by
    intro a
    have hd := (((R.smooth a).differentiable (by simp) x).hasFDerivAt).pow 2
    rw [hd.fderiv]
    simp only [smul_apply, smul_eq_mul, R.directional]
    by_cases hab : a = b <;> simp [hab]
  simp_rw [heach]
  simp

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_RegularizedHardyField
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

noncomputable def regularizedHardyField {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (ε : ℝ) (b : Fin 3) (x : Configuration n) : ℝ :=
  R.coord b x / (blockRadiusSq i R x + ε)

lemma contDiff_regularizedHardyField {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (b : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedHardyField i R ε b) := by
  exact (R.smooth b).div ((contDiff_blockRadiusSq i R).add contDiff_const)
    (fun x => ne_of_gt (add_pos_of_nonneg_of_pos (blockRadiusSq_nonneg i R x) hε))

lemma fderiv_regularizedHardyField {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (b : Fin 3) (x : Configuration n) :
    fderiv ℝ (regularizedHardyField i R ε b) x (EuclideanSpace.single (i,b) 1) =
      (blockRadiusSq i R x + ε)⁻¹ -
        2 * (R.coord b x)^2 / (blockRadiusSq i R x + ε)^2 := by
  have hd := ((contDiff_blockRadiusSq i R).differentiable (by first | simp | exact_mod_cast le_top) x).hasFDerivAt.add_const ε
  have hne : blockRadiusSq i R x + ε ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (blockRadiusSq_nonneg i R x) hε)
  have hi := (hasFDerivAt_inv hne).comp x hd
  have hn := ((R.smooth b).differentiable (by simp) x).hasFDerivAt
  have hm := hn.fun_mul hi
  change fderiv ℝ (fun y : Configuration n =>
    R.coord b y * (blockRadiusSq i R y + ε)⁻¹) x _ = _
  simp only [Function.comp_apply] at hm
  rw [hm.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    ContinuousLinearMap.toSpanSingleton_apply]
  rw [fderiv_blockRadiusSq, R.directional]
  simp only [ite_true, if_true, mul_one]
  ring

lemma regularizedHardyField_sq_sum {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (ε : ℝ) (x : Configuration n) :
    (∑ b : Fin 3, (regularizedHardyField i R ε b x)^2) =
      blockRadiusSq i R x / (blockRadiusSq i R x + ε)^2 := by
  simp only [regularizedHardyField, div_pow, ← Finset.sum_div]
  rfl

lemma regularizedHardyField_divergence {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (x : Configuration n) :
    (∑ b : Fin 3, fderiv ℝ (regularizedHardyField i R ε b) x
      (EuclideanSpace.single (i,b) 1)) =
      (blockRadiusSq i R x + 3 * ε) / (blockRadiusSq i R x + ε)^2 := by
  simp_rw [fderiv_regularizedHardyField i R hε]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_div, ← Finset.mul_sum]
  change 3 * (blockRadiusSq i R x + ε)⁻¹ -
    2 * blockRadiusSq i R x / (blockRadiusSq i R x + ε)^2 = _
  have hne : blockRadiusSq i R x + ε ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (blockRadiusSq_nonneg i R x) hε)
  field_simp
  ring

lemma regularizedHardyField_weight {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (x : Configuration n) :
    (blockRadiusSq i R x + ε)⁻¹ ≤
      2 * (∑ b : Fin 3, fderiv ℝ (regularizedHardyField i R ε b) x
        (EuclideanSpace.single (i,b) 1)) -
      ∑ b : Fin 3, (regularizedHardyField i R ε b x)^2 := by
  rw [regularizedHardyField_divergence i R hε, regularizedHardyField_sq_sum]
  have hpos : 0 < blockRadiusSq i R x + ε :=
    add_pos_of_nonneg_of_pos (blockRadiusSq_nonneg i R x) hε
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hpos)).mp
  field_simp
  nlinarith

lemma integrable_smooth_mul_compact_deriv {n : ℕ} (u F : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u)
    (hF : Continuous F) (v : Configuration n) :
    Integrable (fun x => F x * fderiv ℝ u x v) := by
  exact (hF.mul ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport (huC.fderiv_apply ℝ v).mul_left

lemma integrable_smooth_deriv_mul_compact {n : ℕ} (u F : Configuration n → ℝ)
    (hu : Continuous u) (huC : HasCompactSupport u)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (v : Configuration n) :
    Integrable (fun x => fderiv ℝ F x v * u x) := by
  exact (((hF.continuous_fderiv (by simp)).clm_apply continuous_const).mul hu).integrable_of_hasCompactSupport huC.mul_left

lemma integral_compact_ibp {n : ℕ} (u F : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (v : Configuration n) :
    (∫ x, F x * fderiv ℝ u x v) = -(∫ x, fderiv ℝ F x v * u x) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_smooth_deriv_mul_compact u F hu.continuous huC hF v
  · exact integrable_smooth_mul_compact_deriv u F hu huC hF.continuous v
  · exact (hF.continuous.mul hu.continuous).integrable_of_hasCompactSupport huC.mul_left
  · intro x _; exact hF.differentiable (by simp) x
  · intro x _; exact hu.differentiable (by simp) x

lemma smooth_square_fderiv {n : ℕ} (u : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x v : Configuration n) :
    fderiv ℝ (fun y => (u y)^2) x v = 2 * u x * fderiv ℝ u x v := by
  rw [((hu.differentiable (by simp) x).hasFDerivAt.pow 2).fderiv]
  simp only [smul_apply, smul_eq_mul, Nat.reduceSub, pow_one, nsmul_eq_mul,
    Nat.cast_ofNat]

lemma integral_compact_ibp_deriv_form {n : ℕ} (u F : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (v : Configuration n) :
    (∫ x, fderiv ℝ F x v * u x + F x * fderiv ℝ u x v) = 0 := by
  rw [integral_add
    (integrable_smooth_deriv_mul_compact u F hu.continuous huC hF v)
    (integrable_smooth_mul_compact_deriv u F hu huC hF.continuous v),
    integral_compact_ibp u F hu huC hF v]
  exact add_neg_cancel _

lemma integral_compact_ibp_square {n : ℕ} (u F : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (v : Configuration n) :
    (∫ x, fderiv ℝ F x v * (u x)^2 + 2 * F x * u x * fderiv ℝ u x v) = 0 := by
  have hu2 : ContDiff ℝ (⊤ : ℕ∞) (fun x => (u x)^2) := hu.pow 2
  have hu2C : HasCompactSupport (fun x => (u x)^2) := huC.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have heq := integral_compact_ibp_deriv_form (fun x => (u x)^2) F hu2 hu2C hF v
  calc
    _ = (∫ x, fderiv ℝ F x v * (u x)^2 + F x * fderiv ℝ (fun y => (u y)^2) x v) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [smooth_square_fderiv u hu]
      ring
    _ = 0 := heq

lemma hardy_pointwise_algebra {ι : Type*} [Fintype ι]
    (u w : ℝ) (F D G : ι → ℝ)
    (hw : w ≤ 2 * ∑ b, D b - ∑ b, (F b)^2) :
    w * u^2 ≤ 4 * ∑ b, (G b)^2 +
      2 * ∑ b, (D b * u^2 + 2 * F b * u * G b) := by
  have hs : 0 ≤ ∑ b, (2 * G b + F b * u)^2 :=
    Finset.sum_nonneg (fun b _ => sq_nonneg _)
  have hid : (∑ b, (2 * G b + F b * u)^2) =
      4 * ∑ b, (G b)^2 + 4 * u * ∑ b, F b * G b +
        u^2 * ∑ b, (F b)^2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hid2 : (∑ b, (D b * u^2 + 2 * F b * u * G b)) =
      u^2 * ∑ b, D b + 2 * u * ∑ b, F b * G b := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hp := mul_nonneg (sub_nonneg.mpr hw) (sq_nonneg u)
  rw [hid] at hs
  rw [hid2]
  nlinarith

lemma regularizedHardy_pointwise {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (u : Configuration n → ℝ) (x : Configuration n) :
    (blockRadiusSq i R x + ε)⁻¹ * (u x)^2 ≤
      4 * ∑ b : Fin 3, (fderiv ℝ u x (EuclideanSpace.single (i,b) 1))^2 +
      2 * ∑ b : Fin 3,
        (fderiv ℝ (regularizedHardyField i R ε b) x (EuclideanSpace.single (i,b) 1) *
          (u x)^2 + 2 * regularizedHardyField i R ε b x * u x *
          fderiv ℝ u x (EuclideanSpace.single (i,b) 1)) :=
  hardy_pointwise_algebra (u x) (blockRadiusSq i R x + ε)⁻¹
    (fun b => regularizedHardyField i R ε b x)
    (fun b => fderiv ℝ (regularizedHardyField i R ε b) x (EuclideanSpace.single (i,b) 1))
    (fun b => fderiv ℝ u x (EuclideanSpace.single (i,b) 1))
    (regularizedHardyField_weight i R hε x)

lemma integrable_compact_deriv_sq {n : ℕ} (u : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u) (v : Configuration n) :
    Integrable (fun x => (fderiv ℝ u x v)^2) := by
  have hc : Continuous (fun x => fderiv ℝ u x v) :=
    (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hs : HasCompactSupport (fun x => fderiv ℝ u x v) := huC.fderiv_apply ℝ v
  have hs2 : HasCompactSupport (fun x => (fderiv ℝ u x v)^2) :=
    hs.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  exact (hc.pow 2).integrable_of_hasCompactSupport hs2

lemma integrable_compact_ibp_square {n : ℕ} (u F : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (v : Configuration n) :
    Integrable (fun x => fderiv ℝ F x v * (u x)^2 +
      2 * F x * u x * fderiv ℝ u x v) := by
  have hu2C : HasCompactSupport (fun x => (u x)^2) :=
    huC.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have h1 := integrable_smooth_deriv_mul_compact (fun x => (u x)^2)
    F (hu.pow 2).continuous hu2C hF v
  have h2 := integrable_smooth_mul_compact_deriv u (fun x => 2 * F x * u x)
    hu huC ((continuous_const.mul hF.continuous).mul hu.continuous) v
  exact h1.add h2

lemma integral_hardy_algebra {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (W : X → ℝ) (G D : ι → X → ℝ)
    (hW : Integrable W μ) (hG : ∀ b, Integrable (G b) μ)
    (hD : ∀ b, Integrable (D b) μ) (hD0 : ∀ b, (∫ x, D b x ∂μ) = 0)
    (hle : ∀ x, W x ≤ 4 * ∑ b, G b x + 2 * ∑ b, D b x) :
    (∫ x, W x ∂μ) ≤ 4 * ∑ b, ∫ x, G b x ∂μ := by
  have hGs : Integrable (fun x => ∑ b, G b x) μ :=
    integrable_finsetSum _ (fun b _ => hG b)
  have hDs : Integrable (fun x => ∑ b, D b x) μ :=
    integrable_finsetSum _ (fun b _ => hD b)
  have h := integral_mono hW ((hGs.const_mul 4).add (hDs.const_mul 2)) hle
  simp only [Pi.add_apply] at h
  rw [integral_add (hGs.const_mul 4) (hDs.const_mul 2),
    integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun b _ => hG b),
    integral_finsetSum _ (fun b _ => hD b)] at h
  simpa only [hD0, Finset.sum_const_zero, mul_zero, add_zero] using h

lemma integrable_compact_regularized_weight {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (u : Configuration n → ℝ)
    (hu : Continuous u) (huC : HasCompactSupport u) :
    Integrable (fun x => (blockRadiusSq i R x + ε)⁻¹ * (u x)^2) := by
  have hwcont : Continuous (fun x => (blockRadiusSq i R x + ε)⁻¹) :=
    ((contDiff_blockRadiusSq i R).continuous.add continuous_const).inv₀
      (fun x => ne_of_gt (add_pos_of_nonneg_of_pos (blockRadiusSq_nonneg i R x) hε))
  have hs : HasCompactSupport (fun x => (u x)^2) :=
    huC.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  exact (hwcont.mul (hu.pow 2)).integrable_of_hasCompactSupport hs.mul_left

lemma smooth_compact_regularized_hardy {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (u : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u) :
    (∫ x, (blockRadiusSq i R x + ε)⁻¹ * (u x)^2) ≤
      4 * ∑ b : Fin 3, ∫ x, (fderiv ℝ u x (EuclideanSpace.single (i,b) 1))^2 := by
  let G : Fin 3 → Configuration n → ℝ := fun b x =>
    (fderiv ℝ u x (EuclideanSpace.single (i,b) 1))^2
  let D : Fin 3 → Configuration n → ℝ := fun b x =>
    fderiv ℝ (regularizedHardyField i R ε b) x (EuclideanSpace.single (i,b) 1) *
      (u x)^2 + 2 * regularizedHardyField i R ε b x * u x *
      fderiv ℝ u x (EuclideanSpace.single (i,b) 1)
  have hG : ∀ b, Integrable (G b) := fun b => integrable_compact_deriv_sq u hu huC
    (EuclideanSpace.single (i,b) 1)
  have hD : ∀ b, Integrable (D b) := fun b => integrable_compact_ibp_square u
    (regularizedHardyField i R ε b) hu huC (contDiff_regularizedHardyField i R hε b)
    (EuclideanSpace.single (i,b) 1)
  have hD0 : ∀ b, (∫ x, D b x) = 0 := fun b => integral_compact_ibp_square u
    (regularizedHardyField i R ε b) hu huC (contDiff_regularizedHardyField i R hε b)
    (EuclideanSpace.single (i,b) 1)
  exact integral_hardy_algebra volume
    (fun x => (blockRadiusSq i R x + ε)⁻¹ * (u x)^2) G D
    (integrable_compact_regularized_weight i R hε u hu.continuous huC)
    hG hD hD0 (regularizedHardy_pointwise i R hε u)

lemma nonneg_fatou_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (F : ℕ → X → ℝ) (C : ℝ)
    (hF : ∀ n, Integrable (F n) μ) (hn : ∀ n x, 0 ≤ F n x)
    (hf : ∀ x, 0 ≤ f x)
    (ht : ∀ x, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x)))
    (hC : ∀ n, (∫ x, F n x ∂μ) ≤ C) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C := by
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hF n).aestronglyMeasurable)
      (Filter.Eventually.of_forall ht)
  have hb : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (F n x)) Filter.atTop ∂μ := by
        apply lintegral_congr
        intro x
        exact ((ENNReal.continuous_ofReal.tendsto _).comp (ht x)).liminf_eq.symm
      _ ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) Filter.atTop :=
        lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal C := by
        apply Filter.liminf_le_of_frequently_le (hu_le := Filter.isBoundedUnder_of ⟨0, fun _ => bot_le⟩)
        apply Filter.Eventually.frequently
        apply Filter.Eventually.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (Filter.Eventually.of_forall (hn n))]
        exact ENNReal.ofReal_le_ofReal (hC n)
  have hfinite : Integrable f μ := ⟨hfm,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf)).2
      (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)⟩
  refine ⟨hfinite, ?_⟩
  have hCn : 0 ≤ C := (integral_nonneg (hn 0)).trans (hC 0)
  rw [← ofReal_integral_eq_lintegral_ofReal hfinite (Filter.Eventually.of_forall hf)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hCn).1 hb

lemma smooth_compact_hardy {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (u : Configuration n → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u) :
    Integrable (fun x => (blockRadiusSq i R x)⁻¹ * (u x)^2) ∧
    (∫ x, (blockRadiusSq i R x)⁻¹ * (u x)^2) ≤
      4 * ∑ b : Fin 3, ∫ x, (fderiv ℝ u x (EuclideanSpace.single (i,b) 1))^2 := by
  let eps : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have heps : ∀ k, 0 < eps k := fun k => one_div_pos.mpr (by positivity)
  let A := {x : Configuration n | blockRadiusSq i R x ≠ 0}
  have hA : MeasurableSet A :=
    ((contDiff_blockRadiusSq i R).continuous.measurable (measurableSet_singleton 0)).compl
  let F : ℕ → Configuration n → ℝ := fun k =>
    A.indicator (fun x => (blockRadiusSq i R x + eps k)⁻¹ * (u x)^2)
  have hF : ∀ k, Integrable (F k) := fun k =>
    (integrable_compact_regularized_weight i R (heps k) u hu.continuous huC).indicator hA
  have hFn : ∀ k x, 0 ≤ F k x := by
    intro k x
    exact Set.indicator_nonneg (fun x _ =>
      mul_nonneg (inv_nonneg.mpr (add_nonneg (blockRadiusSq_nonneg i R x) (heps k).le))
        (sq_nonneg (u x))) x
  have ht : ∀ x, Filter.Tendsto (fun k => F k x) Filter.atTop
      (nhds ((blockRadiusSq i R x)⁻¹ * (u x)^2)) := by
    intro x
    by_cases hx : x ∈ A
    · simp only [F, Set.indicator_of_mem hx]
      have ht0 : Filter.Tendsto eps Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have htt := (Filter.Tendsto.const_add (blockRadiusSq i R x) ht0).inv₀ (by simpa only [A, Set.mem_ofPred_eq, add_zero] using hx)
      simpa only [add_zero] using htt.mul_const ((u x)^2)
    · have hx0 : blockRadiusSq i R x = 0 := by simpa only [A, Set.mem_ofPred_eq, not_not] using hx
      simp only [F, Set.indicator_of_notMem hx, hx0, inv_zero, zero_mul]
      exact tendsto_const_nhds
  apply nonneg_fatou_integrable volume _ F _ hF hFn
    (fun x => mul_nonneg (inv_nonneg.mpr (blockRadiusSq_nonneg i R x)) (sq_nonneg (u x))) ht
  intro k
  calc
    (∫ x, F k x) ≤ ∫ x, (blockRadiusSq i R x + eps k)⁻¹ * (u x)^2 := by
      apply integral_mono (hF k)
        (integrable_compact_regularized_weight i R (heps k) u hu.continuous huC)
      intro x
      exact Set.indicator_le_self' (fun x _ =>
        mul_nonneg (inv_nonneg.mpr (add_nonneg (blockRadiusSq_nonneg i R x) (heps k).le))
          (sq_nonneg (u x))) x
    _ ≤ _ := smooth_compact_regularized_hardy i R (heps k) u hu huC

lemma convolution_sq_le {n : ℕ} (κ u : Configuration n → ℝ)
    (hκ : Continuous κ) (hκC : HasCompactSupport κ)
    (hκn : ∀ x, 0 ≤ κ x) (hκI : (∫ x, κ x) = 1)
    (hu : LocallyIntegrable u) (hu2 : Integrable (fun x => (u x)^2))
    (x : Configuration n) :
    ((κ ⋆ u) x)^2 ≤ (κ ⋆ (fun x => (u x)^2)) x := by
  have h1 : Integrable (fun y => κ (x-y) * u y) := by
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul, mul_comm] using
      hκC.convolutionExists_right (lsmul ℝ ℝ) hu hκ x
  have h2 : Integrable (fun y => κ (x-y) * (u y)^2) := by
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul, mul_comm] using
      hκC.convolutionExists_right (lsmul ℝ ℝ) hu2.locallyIntegrable hκ x
  have h0 : Integrable (fun y => κ (x-y)) :=
    (hκ.integrable_of_hasCompactSupport hκC).comp_sub_left x
  have heq : (∫ y, κ (x-y) * u y) = (κ ⋆ u) x := by
    rw [convolution_eq_swap]
    rfl
  have heq0 : (∫ y, κ (x-y)) = 1 := by
    rw [integral_sub_left_eq_self, hκI]
  have hm : (∫ y, (2 * (κ ⋆ u) x) * (κ (x-y) * u y) -
      ((κ ⋆ u) x)^2 * κ (x-y)) ≤ ∫ y, κ (x-y) * (u y)^2 := by
    apply integral_mono ((h1.const_mul _).sub (h0.const_mul _)) h2
    intro y
    simp only [Pi.sub_apply]
    nlinarith [mul_nonneg (hκn (x-y)) (sq_nonneg (u y - (κ ⋆ u) x))]
  rw [integral_sub (h1.const_mul _) (h0.const_mul _), integral_const_mul,
    integral_const_mul, heq, heq0] at hm
  have heq2 : (κ ⋆ (fun x => (u x)^2)) x = ∫ y, κ (x-y) * (u y)^2 := by
    rw [convolution_eq_swap]
    rfl
  rw [heq2]
  nlinarith

lemma convolution_sq_integral_le {n : ℕ} (κ u : Configuration n → ℝ)
    (hκ : Continuous κ) (hκC : HasCompactSupport κ)
    (hκn : ∀ x, 0 ≤ κ x) (hκI : (∫ x, κ x) = 1)
    (hu : LocallyIntegrable u) (hu2 : Integrable (fun x => (u x)^2)) :
    Integrable (fun x => ((κ ⋆ u) x)^2) ∧
    (∫ x, ((κ ⋆ u) x)^2) ≤ ∫ x, (u x)^2 := by
  have hdom : Integrable (κ ⋆ (fun x => (u x)^2)) :=
    (hκ.integrable_of_hasCompactSupport hκC).integrable_convolution (lsmul ℝ ℝ) hu2
  have hcont : Continuous (κ ⋆ u) :=
    hκC.continuous_convolution_left (lsmul ℝ ℝ) hκ hu
  have hsq : Integrable (fun x => ((κ ⋆ u) x)^2) := by
    apply hdom.mono' (hcont.pow 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact convolution_sq_le κ u hκ hκC hκn hκI hu hu2 x
  refine ⟨hsq, ?_⟩
  calc
    _ ≤ ∫ x, (κ ⋆ (fun x => (u x)^2)) x :=
      integral_mono hsq hdom (convolution_sq_le κ u hκ hκC hκn hκI hu hu2)
    _ = _ := by
      rw [integral_convolution (lsmul ℝ ℝ)
        (hκ.integrable_of_hasCompactSupport hκC) hu2, hκI]
      simp

lemma real_convolution_comm {n : ℕ} (u κ : Configuration n → ℝ) :
    u ⋆ κ = κ ⋆ u := by
  ext x
  rw [convolution_eq_swap, convolution_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => mul_comm _ _)

lemma fderiv_const_sub_comp {n : ℕ} (κ : Configuration n → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (x y v : Configuration n) :
    fderiv ℝ (fun z => κ (x - z)) y v = -(fderiv ℝ κ (x-y) v) := by
  have hd := ((hκ.differentiable (by simp) (x-y)).hasFDerivAt).comp y
    ((hasFDerivAt_id y).const_sub x)
  change HasFDerivAt (fun z => κ (x-z)) _ y at hd
  rw [hd.fderiv]
  simp

lemma weak_convolution_partial {n : ℕ} (u g κ : Configuration n → ℝ)
    (v : Configuration n) (hu : LocallyIntegrable u)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκC : HasCompactSupport κ)
    (hw : ∀ φ : Configuration n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * fderiv ℝ φ x v) = -(∫ x, g x * φ x))
    (x : Configuration n) :
    fderiv ℝ (κ ⋆ u) x v = (κ ⋆ g) x := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun y => κ (x-y)) :=
    hκ.comp (contDiff_const.sub contDiff_id)
  have hφC : HasCompactSupport (fun y => κ (x-y)) :=
    hκC.comp_homeomorph (Homeomorph.subLeft x)
  have ht := hw (fun y => κ (x-y)) hφ hφC
  simp_rw [fderiv_const_sub_comp κ hκ x] at ht
  simp only [mul_neg, integral_neg, neg_inj] at ht
  rw [real_convolution_comm κ u,
    (hκC.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hu (hκ.of_le (by first | simp | exact_mod_cast le_top)) x).fderiv,
    convolution_precompR_apply (lsmul ℝ ℝ) hu (hκC.fderiv ℝ)
      (hκ.continuous_fderiv (by simp)) x v]
  rw [real_convolution_comm κ g]
  simpa only [convolution_def, lsmul_apply, smul_eq_mul] using ht

lemma ae_nonneg_fatou_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (F : ℕ → X → ℝ) (C : ℝ)
    (hF : ∀ n, Integrable (F n) μ) (hn : ∀ n x, 0 ≤ F n x)
    (hf : ∀ x, 0 ≤ f x)
    (ht : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x)))
    (hC : ∀ n, (∫ x, F n x ∂μ) ≤ C) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C := by
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hF n).aestronglyMeasurable)
      ht
  have hb : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (F n x)) Filter.atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ht] with x hx
        exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
      _ ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) Filter.atTop :=
        lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal C := by
        apply Filter.liminf_le_of_frequently_le (hu_le := Filter.isBoundedUnder_of ⟨0, fun _ => bot_le⟩)
        apply Filter.Eventually.frequently
        apply Filter.Eventually.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (Filter.Eventually.of_forall (hn n))]
        exact ENNReal.ofReal_le_ofReal (hC n)
  have hfinite : Integrable f μ := ⟨hfm,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf)).2
      (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)⟩
  refine ⟨hfinite, ?_⟩
  have hCn : 0 ≤ C := (integral_nonneg (hn 0)).trans (hC 0)
  rw [← ofReal_integral_eq_lintegral_ofReal hfinite (Filter.Eventually.of_forall hf)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hCn).1 hb

end Coulomb
end
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

lemma ae_nonneg_fatou_integrable_of_bound_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (F : ℕ → X → ℝ) (C : ℝ) (B : ℕ → ℝ)
    (hF : ∀ n, Integrable (F n) μ) (hn : ∀ n x, 0 ≤ F n x)
    (hf : ∀ x, 0 ≤ f x)
    (ht : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x)))
    (hC : ∀ n, (∫ x, F n x ∂μ) ≤ B n)
    (hB : Filter.Tendsto B Filter.atTop (nhds C)) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C := by
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hF n).aestronglyMeasurable)
      ht
  have hb : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (F n x)) Filter.atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ht] with x hx
        exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
      _ ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) Filter.atTop :=
        lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ Filter.liminf (fun n => ENNReal.ofReal (B n)) Filter.atTop := by
        apply Filter.liminf_le_liminf (hu := Filter.isBoundedUnder_of ⟨0, fun _ => bot_le⟩)
          (hv := Filter.isCoboundedUnder_ge_of_le Filter.atTop (fun _ => le_top))
        apply Filter.Eventually.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (Filter.Eventually.of_forall (hn n))]
        exact ENNReal.ofReal_le_ofReal (hC n)
      _ = ENNReal.ofReal C := ((ENNReal.continuous_ofReal.tendsto C).comp hB).liminf_eq
  have hfinite : Integrable f μ := ⟨hfm,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf)).2
      (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)⟩
  refine ⟨hfinite, ?_⟩
  have hCn : 0 ≤ C := ge_of_tendsto hB
    (Filter.Eventually.of_forall (fun n => (integral_nonneg (hn n)).trans (hC n)))
  rw [← ofReal_integral_eq_lintegral_ofReal hfinite (Filter.Eventually.of_forall hf)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hCn).1 hb

lemma realMemLp_bounded_mul {n : ℕ} (u f : Configuration n → ℝ)
    (hu : MemLp u 2) (hf : Continuous f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    MemLp (fun x => f x * u x) 2 := by
  apply hu.of_le_mul (c := B) (hf.aestronglyMeasurable.mul hu.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  change ‖f x * u x‖ ≤ B * ‖u x‖
  rw [norm_mul, Real.norm_eq_abs (f x)]
  exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

lemma weak_partial_bounded_mul {n : ℕ} (u g f : Configuration n → ℝ)
    (v : Configuration n) (hu : MemLp u 2) (hg : MemLp g 2)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {B D : ℝ} (hB : ∀ x, |f x| ≤ B) (hD : ∀ x, |fderiv ℝ f x v| ≤ D)
    (hw : ∀ φ : Configuration n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * fderiv ℝ φ x v) = -(∫ x, g x * φ x))
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) :
    (∫ x, (f x * u x) * fderiv ℝ φ x v) =
      -(∫ x, (f x * g x + fderiv ℝ f x v * u x) * φ x) := by
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφL : MemLp φ 2 := hφ.continuous.memLp_of_hasCompactSupport hφC
  have hdφL : MemLp (fun x => fderiv ℝ φ x v) 2 :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hφC.fderiv_apply ℝ v)
  have hA : Integrable (fun x => (f x * u x) * fderiv ℝ φ x v) := (realMemLp_bounded_mul u f hu hf.continuous hB).integrable_mul hdφL
  have hB' : Integrable (fun x => (fderiv ℝ f x v * u x) * φ x) := (realMemLp_bounded_mul u _ hu hdf hD).integrable_mul hφL
  have hC : Integrable (fun x => (f x * g x) * φ x) := (realMemLp_bounded_mul g f hg hf.continuous hB).integrable_mul hφL
  have hweak := hw (f * φ) (hf.mul hφ) hφC.mul_left
  have hprod : ∀ x, u x * fderiv ℝ (f * φ) x v =
      (f x * u x) * fderiv ℝ φ x v + (fderiv ℝ f x v * u x) * φ x := by
    intro x
    rw [fderiv_mul (hf.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp_rw [hprod] at hweak
  rw [integral_add hA hB'] at hweak
  have hr : ∀ x, g x * (f * φ) x = (f x * g x) * φ x := by
    intro x
    simp only [Pi.mul_apply]
    ring
  simp_rw [hr] at hweak
  simp_rw [add_mul]
  rw [integral_add hC hB']
  linarith

lemma fderiv_smul_input {n : ℕ} (f : Configuration n → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) (x v : Configuration n) :
    fderiv ℝ (fun z => f (c • z)) x v = c * fderiv ℝ f (c • x) v := by
  have hd := ((hf.differentiable (by simp) (c • x)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).const_smul c)
  change HasFDerivAt (fun z => f (c • z)) _ x at hd
  rw [hd.fderiv]
  simp

lemma exists_hardyCutoffs (n : ℕ) :
    ∃ (χ : ℕ → Configuration n → ℝ) (D : ℝ),
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (χ k)) ∧
      (∀ k, HasCompactSupport (χ k)) ∧
      (∀ k x, |χ k x| ≤ 1) ∧
      (∀ k a x, |fderiv ℝ (χ k) x (EuclideanSpace.single a 1)| ≤ D) ∧
      (∀ x, Filter.Tendsto (fun k => χ k x) Filter.atTop (nhds 1)) ∧
      (∀ a x, Filter.Tendsto (fun k => fderiv ℝ (χ k) x
        (EuclideanSpace.single a 1)) Filter.atTop (nhds 0)) := by
  let β : ContDiffBump (0 : Configuration n) := ⟨1, 2, by norm_num, by norm_num⟩
  let c : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hc : ∀ k, 0 < c k := fun k => one_div_pos.mpr (by positivity)
  have hc1 : ∀ k, c k ≤ 1 := by
    intro k
    simpa only [c, div_one] using
      one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num)
        (show (1 : ℝ) ≤ (k : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hct : Filter.Tendsto c Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hβ : ContDiff ℝ (⊤ : ℕ∞) (β : Configuration n → ℝ) := β.contDiff
  have hβC := β.hasCompactSupport
  have hβ1 : β 0 = 1 := β.one_of_mem_closedBall (by simp [β])
  obtain ⟨D, hD⟩ := ((hβC.fderiv ℝ).isCompact_range
    (hβ.continuous_fderiv (by simp))).exists_bound_of_continuousOn
      (f := fun z => z) continuous_id.continuousOn
  have hD' : ∀ x, ‖fderiv ℝ (β : Configuration n → ℝ) x‖ ≤ D :=
    fun x => hD _ ⟨x, rfl⟩
  have hDn : 0 ≤ D := (norm_nonneg _).trans (hD' 0)
  refine ⟨fun k x => β (c k • x), D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact hβ.comp (contDiff_id.const_smul (c k))
  · intro k
    exact hβC.comp_homeomorph (Homeomorph.smulOfNeZero (c k) (hc k).ne')
  · intro k x
    rw [abs_of_nonneg β.nonneg]
    exact β.le_one
  · intro k a x
    rw [fderiv_smul_input _ hβ, abs_mul, abs_of_pos (hc k)]
    have hnorm : |fderiv ℝ (β : Configuration n → ℝ) (c k • x)
        (EuclideanSpace.single a 1)| ≤ D := by
      calc
        _ = ‖fderiv ℝ (β : Configuration n → ℝ) (c k • x)
          (EuclideanSpace.single a 1)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ (β : Configuration n → ℝ) (c k • x)‖ *
          ‖EuclideanSpace.single (𝕜 := ℝ) a 1‖ := le_opNorm _ _
        _ ≤ D := by simpa using hD' (c k • x)
    exact (mul_le_mul_of_nonneg_left hnorm (hc k).le).trans
      (mul_le_of_le_one_left hDn (hc1 k))
  · intro x
    have ht : Filter.Tendsto (fun k => c k • x) Filter.atTop (nhds 0) := by
      simpa using hct.smul_const x
    simpa only [Function.comp_def, hβ1] using (hβ.continuous.tendsto 0).comp ht
  · intro a x
    have ht : Filter.Tendsto (fun k => c k • x) Filter.atTop (nhds 0) := by
      simpa using hct.smul_const x
    have hdf : Continuous (fun z => fderiv ℝ (β : Configuration n → ℝ) z
        (EuclideanSpace.single a 1)) :=
      (hβ.continuous_fderiv (by simp)).clm_apply continuous_const
    simp_rw [fderiv_smul_input _ hβ]
    simpa only [Function.comp_def, zero_mul] using hct.mul ((hdf.tendsto 0).comp ht)

noncomputable def nuclearHardyCoordinates {n : ℕ} (i : Fin n) (R : Space) :
    HardyCoordinates n i where
  coord b x := x (i,b) - R b
  smooth b := (EuclideanSpace.proj (𝕜 := ℝ) (i,b)).contDiff.sub contDiff_const
  directional a b x := by
    have hd := ((EuclideanSpace.proj (𝕜 := ℝ) (i,a)).hasFDerivAt (x := x)).sub_const (R a)
    simp only [EuclideanSpace.coe_proj] at hd
    rw [hd.fderiv]
    by_cases hab : a = b
    · subst a; simp
    · simp [EuclideanSpace.proj, EuclideanSpace.single, hab]

noncomputable def pairHardyCoordinates {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    HardyCoordinates n i where
  coord b x := x (i,b) - x (j,b)
  smooth b := (EuclideanSpace.proj (𝕜 := ℝ) (i,b)).contDiff.sub
    (EuclideanSpace.proj (𝕜 := ℝ) (j,b)).contDiff
  directional a b x := by
    have hd := ((EuclideanSpace.proj (𝕜 := ℝ) (i,a)).hasFDerivAt (x := x)).sub
      ((EuclideanSpace.proj (𝕜 := ℝ) (j,a)).hasFDerivAt (x := x))
    simp only [EuclideanSpace.coe_proj] at hd
    change HasFDerivAt (fun x => x (i,a) - x (j,a)) _ x at hd
    rw [hd.fderiv]
    by_cases hab : a = b
    · subst a; simp [EuclideanSpace.proj, EuclideanSpace.single, hij.symm]
    · simp [EuclideanSpace.proj, EuclideanSpace.single, hab, hij.symm]

lemma realCLM_mul_ofReal (L : ℂ →L[ℝ] ℝ) (z : ℂ) (t : ℝ) :
    L (z * (t : ℂ)) = L z * t := by
  rw [mul_comm, mul_comm (L z)]
  exact L.map_smul t z

lemma weak_complex_component {n : ℕ} (u g : Configuration n → ℂ)
    (hu : MemLp u 2) (hg : MemLp g 2) (v : Configuration n)
    (hw : ∀ (φ : Configuration n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x v : ℂ)) = -(∫ x, g x * (φ x : ℂ)))
    (L : ℂ →L[ℝ] ℝ) (φ : Configuration n → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) :
    (∫ x, L (u x) * fderiv ℝ φ x v) = -(∫ x, L (g x) * φ x) := by
  have hφL : MemLp (fun x => (φ x : ℂ)) 2 :=
    (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
      (hφC.comp_left (by simp))
  have hdφL : MemLp (fun x => (fderiv ℝ φ x v : ℂ)) 2 :=
    (Complex.continuous_ofReal.comp
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
      ((hφC.fderiv_apply ℝ v).comp_left (by simp))
  have hA := L.integral_comp_comm (hu.integrable_mul hdφL)
  have hB := L.integral_comp_comm (hg.integrable_mul hφL)
  simp only [Pi.mul_apply, realCLM_mul_ofReal] at hA hB
  rw [hA, hw φ hφ hφC, map_neg, ← hB]

noncomputable def hardyCoulomb {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (x : Configuration n) : ℝ := (Real.sqrt (blockRadiusSq i R x))⁻¹

lemma hardyCoulomb_sq {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (x : Configuration n) : (hardyCoulomb i R x)^2 = (blockRadiusSq i R x)⁻¹ := by
  rw [hardyCoulomb, inv_pow, Real.sq_sqrt (blockRadiusSq_nonneg i R x)]

lemma measurable_hardyCoulomb {n : ℕ} (i : Fin n) (R : HardyCoordinates n i) :
    Measurable (hardyCoulomb i R) :=
  (contDiff_blockRadiusSq i R).continuous.measurable.sqrt.inv

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_Add
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

lemma blockRadiusSq_pair {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x : Configuration n) :
    blockRadiusSq i (pairHardyCoordinates i j hij) x = ‖position x i - position x j‖^2 := by
  simp [blockRadiusSq, pairHardyCoordinates, position, EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs]

lemma hardyCoulomb_pair {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x : Configuration n) :
    hardyCoulomb i (pairHardyCoordinates i j hij) x =
      coulombKernel (position x i - position x j) := by
  rw [hardyCoulomb, blockRadiusSq_pair, Real.sqrt_sq (norm_nonneg _)]
  rfl

lemma H1Vector.test_integrable {n : ℕ} (ψ : H1Vector n) (s : Spins n)
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    Integrable (fun x => ψ.value s x * (φ x : ℂ)) := by
  have hL : MemLp (fun x => (φ x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
      (hc.comp_left (by simp))
  exact (ψ.value_L2 s).integrable_mul hL

noncomputable def H1Vector.add {n : ℕ} (ψ φ : H1Vector n) : H1Vector n where
  value s x := ψ.value s x + φ.value s x
  gradient s a x := ψ.gradient s a x + φ.gradient s a x
  value_L2 s := (ψ.value_L2 s).add (φ.value_L2 s)
  partial_L2 s a := (ψ.partial_L2 s a).add (φ.partial_L2 s a)
  weak_partial s a f hf hc := by
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x (EuclideanSpace.single a 1)) :=
      (hf.fderiv_right (by first | simp | exact_mod_cast le_top)).clm_apply contDiff_const
    have hdc := hc.fderiv_apply ℝ (EuclideanSpace.single a 1)
    have hiψ := ψ.test_integrable s _ hd hdc
    have hiφ := φ.test_integrable s _ hd hdc
    have hL : MemLp (fun x => (f x : ℂ)) 2 volume :=
      (Complex.continuous_ofReal.comp hf.continuous).memLp_of_hasCompactSupport
        (hc.comp_left (by simp))
    have hjψ := (ψ.partial_L2 s a).integrable_mul hL
    have hjφ := (φ.partial_L2 s a).integrable_mul hL
    change Integrable (fun x => ψ.gradient s a x * (f x : ℂ)) at hjψ
    change Integrable (fun x => φ.gradient s a x * (f x : ℂ)) at hjφ
    simp_rw [add_mul]
    rw [integral_add hiψ hiφ, integral_add hjψ hjφ,
      ψ.weak_partial s a f hf hc, φ.weak_partial s a f hf hc]
    ring

noncomputable def H1Vector.rsmul {n : ℕ} (t : ℝ) (ψ : H1Vector n) : H1Vector n where
  value s x := (t : ℂ) * ψ.value s x
  gradient s a x := (t : ℂ) * ψ.gradient s a x
  value_L2 s := memLp_two_real_mul (ψ.value_L2 s) continuous_const (fun _ => le_rfl)
  partial_L2 s a := memLp_two_real_mul (ψ.partial_L2 s a) continuous_const (fun _ => le_rfl)
  weak_partial s a f hf hc := by
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_const_mul, ψ.weak_partial s a f hf hc]
    ring

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SmoothCutoffApproximation
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

theorem cutoff_complex_C1 {n : ℕ} (χ : Configuration n → ℝ)
    (hχ : ContDiff ℝ 1 χ) : ContDiff ℝ 1 (fun x => (χ x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hχ

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

def FermionicCoefficients {n : ℕ} {α : Type*} (f : (Fin n → α) → ℂ) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)) b, f (b ∘ p) = ((p.sign : ℤ) : ℂ) * f b

noncomputable def coefficientPermEquiv {n : ℕ} {α : Type*} (p : Equiv.Perm (Fin n)) :
    (Fin n → α) ≃ (Fin n → α) where
  toFun b := b ∘ p
  invFun b := b ∘ p.symm
  left_inv b := by ext i; simp
  right_inv b := by ext i; simp

noncomputable def permuteIsometry {n : ℕ} (p : Equiv.Perm (Fin n)) :
    Configuration n ≃ₗᵢ[ℝ] Configuration n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p.symm.prodCongr (Equiv.refl (Fin 3)))

noncomputable def spinPermEquiv {n : ℕ} (p : Equiv.Perm (Fin n)) : Spins n ≃ Spins n where
  toFun s := s ∘ p
  invFun s := s ∘ p.symm
  left_inv s := by ext i; simp
  right_inv s := by ext i; simp

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

theorem measurePreserving_uncurry {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Type*} [MeasurableSpace A] (μ : ι → κ → Measure A)
    [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.curry ι κ A).symm
      (Measure.pi fun i => Measure.pi (μ i))
      (Measure.pi fun ij : ι × κ => μ ij.1 ij.2) := by
  refine ⟨(MeasurableEquiv.curry ι κ A).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [MeasurableEquiv.map_apply]
  have he : (MeasurableEquiv.curry ι κ A).symm ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s (i,j))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
      MeasurableEquiv.coe_curry_symm, Function.uncurry_apply_pair, Prod.forall]
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  simpa only [Finset.univ_product_univ] using
    (Finset.prod_product Finset.univ Finset.univ (fun ij : ι × κ => μ ij.1 ij.2 (s ij))).symm

abbrev StateHilbert (n : ℕ) := PiLp 2 (fun _ : Spins n => Lp ℂ 2 (volume : Measure (Configuration n)))

noncomputable def H1Vector.toHilbert {n : ℕ} (ψ : H1Vector n) : StateHilbert n :=
  WithLp.toLp 2 (fun s => (ψ.value_L2 s).toLp (ψ.value s))

lemma inner_toLp_complex {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f g : A → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ x, star (f x) * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]

section FiberContraction
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]

noncomputable def fiberContract (v : A → ℂ) (f : B × A → ℂ) (b : B) : ℂ :=
  ∫ a, star (v a) * f (b, a) ∂μ

end FiberContraction

def CompleteOrbitals {A ι : Type*} [MeasurableSpace A] (μ : Measure A)
    (v : ι → A → ℂ) : Prop :=
  ∀ f : A → ℂ, MemLp f 2 μ → (∀ i, (∫ a, star (v i a) * f a ∂μ) = 0) → f =ᵐ[μ] 0

lemma scalarTensor_memLp {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (b : Fin n → ι) :
    MemLp (fun x : Fin n → A => ∏ i, v (b i) (x i)) 2 (Measure.pi fun _ => μ) := by
  have hm : AEStronglyMeasurable (fun x : Fin n → A => ∏ i, v (b i) (x i))
      (Measure.pi fun _ => μ) := by
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (hv (b i)).aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => μ) i)
  apply (memLp_two_iff_integrable_sq_norm hm).2
  simpa only [norm_prod, ← Finset.prod_pow] using
    Integrable.fintype_prod (fun i => (hv (b i)).norm.integrable_sq)

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_BlockIndex
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
namespace Coulomb
noncomputable def blockIndex (m k : ℕ) :
    (Fin m × Fin 3) ⊕ (Fin k × Fin 3) ≃ Fin (m+k) × Fin 3 :=
  (Equiv.sumProdDistrib (Fin m) (Fin k) (Fin 3)).symm.trans
    (Equiv.prodCongr finSumFinEquiv (Equiv.refl _))

noncomputable def joinConfiguration (m k : ℕ) :
    (Configuration m × Configuration k) ≃L[ℝ] Configuration (m+k) :=
  EuclideanSpace.sumEquivProd.symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (blockIndex m k)).toContinuousLinearEquiv

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_OrbitalHilbertBasis
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

noncomputable def orbitalHilbertBasis {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) : HilbertBasis ι ℂ (Lp ℂ 2 μ) :=
  HilbertBasis.mkOfOrthogonalEqBot (v := fun i => (hv i).toLp (v i))
    (by rw [orthonormal_iff_ite]; intro i j; rw [inner_toLp_complex]; exact ho i j)
    (by
      apply (Submodule.eq_bot_iff _).mpr
      intro f hf
      apply Lp.eq_zero_iff_ae_eq_zero.mpr
      apply hc f (Lp.memLp f)
      intro i
      have he := (Submodule.mem_orthogonal _ _).1 hf ((hv i).toLp (v i))
        (Submodule.subset_span (Set.mem_range_self i))
      have hi := inner_toLp_complex (hv i) (Lp.memLp f)
      simp only [Lp.toLp_coeFn] at hi
      rwa [hi] at he)

section GeneralFermionSpace
variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]

noncomputable def scalarCoefficient {n : ℕ} (f : (Fin n → A) → ℂ)
    (v : ι → A → ℂ) (b : Fin n → ι) : ℂ :=
  ∫ x, star (∏ i, v (b i) (x i)) * f x ∂(Measure.pi fun _ => μ)

def ProductAntisymmetric {n : ℕ} (f : (Fin n → A) → ℂ) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)), ∀ᵐ x ∂(Measure.pi fun _ => μ),
    f (x ∘ p) = ((p.sign : ℤ) : ℂ) * f x

end GeneralFermionSpace

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_TsumFixed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)

include hv in
lemma orbital_sum_memLp (s : Finset ι) (c : ι → ℂ) :
    MemLp (fun x => ∑ i ∈ s, c i * v i x) 2 μ :=
  memLp_finsetSum s (fun i _ => (hv i).const_mul (c i))

end Coulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_ThomasFermi_FirstFiber
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

noncomputable def firstFiber {A : Type*} {n : ℕ} (f : (Fin (n+1) → A) → ℂ)
    (z : (Fin n → A) × A) : ℂ := f (Fin.cons z.2 z.1)

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_SpinCubeEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb

noncomputable def spinCubeEquiv (n : ℕ) :
    (Fin n → (Fin 2 × (Fin 3 → ℝ))) ≃ᵐ (Spins n × ((Fin n × Fin 3) → ℝ)) :=
  (MeasurableEquiv.arrowProdEquivProdArrow (Fin 2) (Fin 3 → ℝ) (Fin n)).trans
    ((MeasurableEquiv.refl (Spins n)).prodCongr (MeasurableEquiv.curry (Fin n) (Fin 3) ℝ).symm)

noncomputable def cubeState {n : ℕ} (ψ : H1Vector n)
    (z : Fin n → (Fin 2 × (Fin 3 → ℝ))) : ℂ :=
  ψ.value (fun i => (z i).1) (WithLp.toLp 2 (fun ij => (z ij.1).2 ij.2))

end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_Translate
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
namespace Coulomb

noncomputable def spinSpaceMeasure : Measure (Fin 2 × (Fin 3 → ℝ)) := Measure.count.prod volume
instance spinSpaceMeasure_sigmaFinite : SigmaFinite spinSpaceMeasure := by
  unfold spinSpaceMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_CoreSliceRegular
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
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal

open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

def H1Vector.CoreSliceRegular {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    (x : Configuration m) : Prop :=
      (∀ t : Spins k, MemLp (fun y => ψ.value (Fin.append s t) (joinConfiguration m k (x,y))) 2 volume) ∧
      (∀ (t : Spins k) (a : Fin k × Fin 3),
        MemLp (fun y => ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
          (joinConfiguration m k (x,y))) 2 volume ∧
        ∀ (φ : Configuration k → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ y, ψ.value (Fin.append s t) (joinConfiguration m k (x,y)) *
          (fderiv ℝ φ y (EuclideanSpace.single a 1) : ℂ)) =
        -(∫ y, ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
          (joinConfiguration m k (x,y)) * (φ y : ℂ)))

noncomputable def H1Vector.zero (n : ℕ) : H1Vector n where
  value := fun _ _ => 0
  gradient := fun _ _ _ => 0
  value_L2 := fun _ => MemLp.zero'
  partial_L2 := fun _ _ => MemLp.zero'
  weak_partial := by intros; simp

noncomputable def H1Vector.coreSlice {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    (x : Configuration m) : H1Vector k := by
  classical
  exact if h : ψ.CoreSliceRegular s x then
    { value := fun t y => ψ.value (Fin.append s t) (joinConfiguration m k (x,y))
      gradient := fun t a y => ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
        (joinConfiguration m k (x,y))
      value_L2 := h.1
      partial_L2 := fun t a => (h.2 t a).1
      weak_partial := fun t a => (h.2 t a).2 }
  else H1Vector.zero k

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_CorePerm
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
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

noncomputable def H1Vector.normalized {n : ℕ} (ψ : H1Vector n) : H1Vector n :=
  ψ.rsmul (Real.sqrt (mass ψ))⁻¹

noncomputable def potentialForm {n : ℕ} (V : Configuration n → ℝ) (ψ : H1Vector n) : ℝ :=
  ∑ s, ∫ x, V x * ‖ψ.value s x‖^2

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_Pullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
namespace Coulomb

lemma linear_form_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : EuclideanSpace ℝ ι →L[ℝ] ℝ) (v : EuclideanSpace ℝ ι) :
    T v = ∑ a, v a * T (EuclideanSpace.single a 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, smul_eq_mul]

lemma H1Vector.weak_directional {n : ℕ} (ψ : H1Vector n) (s : Spins n)
    (v : Configuration n) (φ : Configuration n → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
    (∫ x, ψ.value s x * (fderiv ℝ φ x v : ℂ)) =
      -(∫ x, (∑ a, (v a : ℂ) * ψ.gradient s a x) * (φ x : ℂ)) := by
  have hφL : MemLp (fun x => (φ x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
      (hcφ.comp_left (by simp))
  have hdφL (a : Fin n × Fin 3) :
      MemLp (fun x => (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
      ((hcφ.fderiv_apply ℝ _).comp_left (by simp))
  have Hd (x : Configuration n) := linear_form_eq_sum (fderiv ℝ φ x) v
  simp_rw [Hd, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
    Finset.sum_mul]
  have hA (a : Fin n × Fin 3) : Integrable (fun x => ψ.value s x *
      ((v a : ℂ) * (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ))) := by
    simpa only [Pi.mul_apply, mul_left_comm] using ((ψ.value_L2 s).integrable_mul (hdφL a)).const_mul (v a : ℂ)
  have hB (a : Fin n × Fin 3) : Integrable (fun x =>
      ((v a : ℂ) * ψ.gradient s a x) * (φ x : ℂ)) :=
    by simpa only [Pi.mul_apply, mul_assoc] using ((ψ.partial_L2 s a).integrable_mul hφL).const_mul (v a : ℂ)
  rw [integral_finsetSum _ (fun a _ => hA a), integral_finsetSum _ (fun a _ => hB a),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [mul_left_comm (ψ.value s _) (v a : ℂ), mul_assoc]
  rw [integral_const_mul, integral_const_mul, ψ.weak_partial s a φ hφ hcφ]
  ring

lemma H1Vector.weak_partial_isometry {n : ℕ} (ψ : H1Vector n)
    (L : Configuration n ≃ₗᵢ[ℝ] Configuration n) (s : Spins n) (a : Fin n × Fin 3)
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
    (∫ x, ψ.value s (L x) * (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) =
      -(∫ x, (∑ k, ((L (EuclideanSpace.single a 1)) k : ℂ) * ψ.gradient s k (L x)) * (φ x : ℂ)) := by
  let Φ : Configuration n → ℝ := fun y => φ (L.symm y)
  have HΦ : ContDiff ℝ (⊤ : ℕ∞) Φ := hφ.comp L.symm.contDiff
  have HC : HasCompactSupport Φ := hcφ.comp_homeomorph L.symm.toHomeomorph
  have Hd (y : Configuration n) : fderiv ℝ Φ y (L (EuclideanSpace.single a 1)) =
      fderiv ℝ φ (L.symm y) (EuclideanSpace.single a 1) := by
    change fderiv ℝ (φ ∘ L.symm) y _ = _
    rw [fderiv_comp y (hφ.differentiable (by simp)).differentiableAt L.symm.differentiableAt]
    rw [show fderiv ℝ (⇑L.symm) y = L.symm.toContinuousLinearEquiv.toContinuousLinearMap from
      L.symm.toContinuousLinearEquiv.toContinuousLinearMap.fderiv]
    simp
  have H := ψ.weak_directional s (L (EuclideanSpace.single a 1)) Φ HΦ HC
  simp_rw [Hd] at H
  have mp : MeasurePreserving L.toHomeomorph.toMeasurableEquiv volume volume := L.measurePreserving
  rw [← mp.integral_comp' (fun y => ψ.value s y *
      (fderiv ℝ φ (L.symm y) (EuclideanSpace.single a 1) : ℂ)),
    ← mp.integral_comp' (fun y => (∑ k, ((L (EuclideanSpace.single a 1)) k : ℂ) *
      ψ.gradient s k y) * (Φ y : ℂ))] at H
  simpa [Φ] using H

noncomputable def H1Vector.pullback {n : ℕ} (ψ : H1Vector n)
    (L : Configuration n ≃ₗᵢ[ℝ] Configuration n) : H1Vector n where
  value := fun s x => ψ.value s (L x)
  gradient := fun s a x => ∑ k, ((L (EuclideanSpace.single a 1)) k : ℂ) * ψ.gradient s k (L x)
  value_L2 := fun s => (ψ.value_L2 s).comp_measurePreserving L.measurePreserving
  partial_L2 := fun s _a => memLp_finsetSum _ (fun k _ =>
    ((ψ.partial_L2 s k).comp_measurePreserving L.measurePreserving).const_mul _)
  weak_partial := ψ.weak_partial_isometry L

noncomputable section
lemma test_L2 {n : ℕ} {φ : Configuration n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hC : HasCompactSupport φ) :
    MemLp (fun x => (φ x : ℂ)) 2 volume :=
  (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
    (hC.comp_left Complex.ofReal_zero)

lemma test_derivative_L2 {n : ℕ} {φ : Configuration n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hC : HasCompactSupport φ) (a : Configuration n) :
    MemLp (fun x => (fderiv ℝ φ x a : ℂ)) 2 volume :=
  (Complex.continuous_ofReal.comp
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
    ((hC.fderiv_apply ℝ a).comp_left Complex.ofReal_zero)

def H1Vector.scale {n : ℕ} (c : ℂ) (u : H1Vector n) : H1Vector n where
  value := fun s x => c*u.value s x
  gradient := fun s a x => c*u.gradient s a x
  value_L2 := fun s => (u.value_L2 s).const_mul c
  partial_L2 := fun s a => (u.partial_L2 s a).const_mul c
  weak_partial := by
    intro s a φ hφ hC
    simp_rw [mul_assoc, integral_const_mul, u.weak_partial s a φ hφ hC]
    ring

def H1Vector.finiteSum {n : ℕ} {ι : Type*} [Fintype ι] (u : ι → H1Vector n) : H1Vector n where
  value := fun s x => ∑ i, (u i).value s x
  gradient := fun s a x => ∑ i, (u i).gradient s a x
  value_L2 := fun s => memLp_finsetSum _ (fun i _ => (u i).value_L2 s)
  partial_L2 := fun s a => memLp_finsetSum _ (fun i _ => (u i).partial_L2 s a)
  weak_partial := by
    intro s a φ hφ hC
    simp only [Finset.sum_mul]
    rw [integral_finsetSum (f := fun i x => (u i).value s x *
        (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) _ (fun i _ => (u i).value_L2 s |>.integrable_mul
      (test_derivative_L2 hφ hC (EuclideanSpace.single a 1))),
      integral_finsetSum (f := fun i x => (u i).gradient s a x * (φ x : ℂ))
        _ (fun i _ => (u i).partial_L2 s a |>.integrable_mul
      (test_L2 hφ hC))]
    simp_rw [H1Vector.weak_partial _ _ _ _ hφ hC]
    rw [Finset.sum_neg_distrib]

def permutationIsometry {n : ℕ} (p : Equiv.Perm (Fin n)) :
    Configuration n ≃ₗᵢ[ℝ] Configuration n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.prodCongr p.symm (Equiv.refl _))

def H1Vector.permutation {n : ℕ} (u : H1Vector n) (p : Equiv.Perm (Fin n)) : H1Vector n where
  value := fun s => (u.pullback (permutationIsometry p)).value (s ∘ p)
  gradient := fun s => (u.pullback (permutationIsometry p)).gradient (s ∘ p)
  value_L2 := fun s => (u.pullback (permutationIsometry p)).value_L2 (s ∘ p)
  partial_L2 := fun s a => (u.pullback (permutationIsometry p)).partial_L2 (s ∘ p) a
  weak_partial := fun s a φ hφ hC =>
    (u.pullback (permutationIsometry p)).weak_partial (s ∘ p) a φ hφ hC

def permutationSpins {n : ℕ} (p : Equiv.Perm (Fin n)) : Spins n ≃ Spins n :=
  Equiv.arrowCongr p.symm (Equiv.refl _)
end
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Propagation_NuclearPotential
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

namespace Coulomb
def nuclearPotential {M n : ℕ} (S : Nuclei M) (x : Configuration n) : ℝ :=
  ∑ i, attraction S (position x i)
def pairPotential {n : ℕ} (x : Configuration n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i < j then coulombKernel (position x i-position x j) else 0

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FormDomain_CoreKinetic
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
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

noncomputable def coreKinetic {m k : ℕ} (ψ : H1Vector (m+k)) : ℝ :=
  (1/2 : ℝ) * ∑ st : Spins (m+k), ∑ a : Fin k × Fin 3,
    ∫ z, ‖ψ.gradient st (Fin.natAdd m a.1,a.2) z‖^2

end Coulomb

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

def coreOrbitalCoefficient {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (φ : Lp ℂ 2 (volume : Measure (Configuration 1)))
    (s : SpinConfiguration n) (t : SpinConfiguration 1) (x : Configuration n) : ℂ :=
  ∫ y, star (φ y)*u.value (Fin.append s t) (Coulomb.joinConfiguration n 1 (x,y))

end ContinuumCoulomb

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

def chargePrimitive (r : ℝ) : ℝ := r^3*(1+r^2)^(-3/2 : ℝ)

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_PairRegroup
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
noncomputable def pairRegroup {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] : (A × B) × (C × D) ≃ᵐ (A × C) × (B × D) where
  toFun p := ((p.1.1,p.2.1),(p.1.2,p.2.2))
  invFun p := ((p.1.1,p.2.1),(p.1.2,p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by change Measurable (fun p : (A × B) × (C × D) => ((p.1.1,p.2.1),(p.1.2,p.2.2))); fun_prop
  measurable_invFun := by change Measurable (fun p : (A × C) × (B × D) => ((p.1.1,p.2.1),(p.1.2,p.2.2))); fun_prop
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

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

lemma complex_smooth_compact_ibp {n : ℕ} (f : Configuration n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hC : HasCompactSupport f)
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφC : HasCompactSupport φ) (v : Configuration n) :
    (∫ x, f x * (fderiv ℝ φ x v : ℂ)) =
      -(∫ x, fderiv ℝ f x v * (φ x : ℂ)) := by
  let g : Configuration n → ℂ := fun x => (φ x : ℂ)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := Complex.ofRealCLM.contDiff.comp hφ
  have hgC : HasCompactSupport g := hφC.comp_left Complex.ofReal_zero
  have hd (x : Configuration n) : fderiv ℝ g x v = (fderiv ℝ φ x v : ℂ) := by
    exact congrArg (fun L : Configuration n →L[ℝ] ℂ => L v)
      ((Complex.ofRealCLM.hasFDerivAt.comp x ((hφ.differentiable (by simp)) x).hasFDerivAt).fderiv)
  have hf' : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hg' : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi1 : Integrable (fun x => fderiv ℝ f x v * g x) volume := (hf'.mul hg.continuous).integrable_of_hasCompactSupport
    (hgC.mul_left (f := fun x => fderiv ℝ f x v))
  have hi2 : Integrable (fun x => f x * fderiv ℝ g x v) volume := (hf.continuous.mul hg').integrable_of_hasCompactSupport
    (hC.mul_right (f' := fun x => fderiv ℝ g x v))
  have hi3 : Integrable (fun x => f x * g x) volume := (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport
    (hC.mul_right (f' := g))
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi1 hi2 hi3
    (fun x _ => (hf.differentiable (by simp)) x)
    (fun x _ => (hg.differentiable (by simp)) x)
  simpa only [hd] using h

noncomputable def H1Vector.ofSmoothCompact {n : ℕ} (f : Spins n → Configuration n → ℂ)
    (hf : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (f s))
    (hC : ∀ s, HasCompactSupport (f s)) : H1Vector n where
  value := f
  gradient s a x := fderiv ℝ (f s) x (EuclideanSpace.single a 1)
  value_L2 s := (hf s).continuous.memLp_of_hasCompactSupport (hC s)
  partial_L2 s a :=
    (((hf s).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hC s).fderiv_apply ℝ (EuclideanSpace.single a 1))
  weak_partial s a φ hφ hφC := complex_smooth_compact_ibp (f s) (hf s) (hC s) φ hφ hφC _

noncomputable def flatSpinOrbital (v : Space → Fin 2 → ℂ) : Fin 2 × (Fin 3 → ℝ) → ℂ :=
  fun sx => v (WithLp.toLp 2 sx.2) sx.1

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Localization_TruncatedCoulomb
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

noncomputable def truncatedCoulomb (R : ℝ) (x : Space) : ℝ :=
  (Metric.ball (0:Space) R).indicator coulombKernel x
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_PermOrCompSwapOffTwo
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
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

noncomputable def pairIndexEquiv {I : Type*} [DecidableEq I] (i j : I) (hij : i ≠ j) :
    Fin 2 ≃ {k : I // k = i ∨ k = j} where
  toFun b := if b = 0 then ⟨i, Or.inl rfl⟩ else ⟨j, Or.inr rfl⟩
  invFun k := if k.1 = i then 0 else 1
  left_inv b := by fin_cases b <;> simp [Ne.symm hij]
  right_inv k := by
    rcases k with ⟨k,hk | hk⟩ <;> subst k <;> simp [Ne.symm hij]

noncomputable def pairSelectedEquiv {I A : Type*} [DecidableEq I] [MeasurableSpace A]
    (i j : I) (hij : i ≠ j) : ({k : I // k = i ∨ k = j} → A) ≃ᵐ (A × A) :=
  (MeasurableEquiv.piCongrLeft (fun _ : {k : I // k = i ∨ k = j} => A)
    (pairIndexEquiv i j hij)).symm.trans MeasurableEquiv.finTwoArrow

noncomputable def pairSplit {I A : Type*} [DecidableEq I] [MeasurableSpace A]
    (i j : I) (hij : i ≠ j) : (I → A) ≃ᵐ (A × A) × ({k : I // ¬ (k = i ∨ k = j)} → A) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => A) (fun k => k = i ∨ k = j)).trans
    ((pairSelectedEquiv i j hij).prodCongr (MeasurableEquiv.refl _))

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_Gaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
noncomputable def gaussian (a : ℝ) (x : Space) : ℝ := Real.exp (-a*‖x‖^2)
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarExponentialEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global exponential envelopes at every fixed rate below one, and
integrability of their planar radial envelopes. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarExponentialConstant (a : ℝ) : ℝ := Real.exp a / (1 - a ^ 2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalCappedForm
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

def verticalCapPotential (freq S z : ℝ) : ℝ :=
  (freq^2/2) * min (z^2) (S^2)

def verticalCappedForm (freq S : ℝ) (u : ℝ → ℝ) : ℝ :=
  (1/2 : ℝ) * (∫ z, deriv u z^2) + ∫ z, verticalCapPotential freq S z * u z^2

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

def verticalCutoffTailConstant (freq : ℝ) : ℝ :=
  (4 / Real.sqrt (Real.pi/freq)) * ∫ z : ℝ, Real.exp (-(freq/2)*z^2)

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

def positionRealKinetic (f : Position → ℝ) : ℝ :=
  (1/2:ℝ)*∑ a : Fin 3, ∫ x, (fderiv ℝ f x (EuclideanSpace.single a 1))^2

def positionRealForm (V f : Position → ℝ) : ℝ :=
  positionRealKinetic f+∫ x, V x*f x^2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ComplexFormSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical complex one-electron quadratic form splits exactly into
its real and imaginary parts. Finite real-orbital penalties split as well. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def positionComplexKinetic (f : Position → ℂ) : ℝ :=
  (1/2:ℝ)*∑ a : Fin 3, ∫ x, ‖fderiv ℝ f x (EuclideanSpace.single a 1)‖^2

def positionComplexForm (V : Position → ℝ) (f : Position → ℂ) : ℝ :=
  positionComplexKinetic f+∫ x, V x*‖f x‖^2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OneElectronCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Volume- and kinetic-energy-preserving identification of one-electron
configuration space with physical three-dimensional space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def oneElectronCoordinates : Configuration 1 ≃ₗᵢ[ℝ] Position :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.uniqueProd (Fin 3) (Fin 1))

theorem oneElectronCoordinates_single (a : Fin 3) :
    oneElectronCoordinates (EuclideanSpace.single (0,a) (1:ℝ)) = EuclideanSpace.single a 1 := by
  exact LinearIsometryEquiv.piLpCongrLeft_single _ _ _

def oneElectronPullback (f : Configuration 1 → ℂ) (y : Position) : ℂ :=
  f (oneElectronCoordinates.symm y)

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

def electronSlotKinetic {n : ℕ} (u : Coulomb.H1Vector n) (i : Fin n) : ℝ :=
  (1/2:ℝ)*∑ s, ∑ a : Fin 3, ∫ x, ‖u.gradient s (i,a) x‖^2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteCoefficientCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entrywise perturbation bounds needed when applying the actual symmetric
Gram correction to the two- and four-index orbital coefficients. Polynomial
site-count losses suffice for the logarithmic spacing used here. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def finiteTwoIndexChange {m : ℕ} (A : Fin m → Fin m → ℝ)
    (F : Fin m → Fin m → ℝ) (i j : Fin m) : ℝ :=
  ∑ p, ∑ q, (A i p * A j q) * F p q

def finiteFourIndexChange {m : ℕ} (A : Fin m → Fin m → ℝ)
    (F : Fin m → Fin m → Fin m → Fin m → ℝ) (i j k l : Fin m) : ℝ :=
  ∑ p, ∑ q, ∑ r, ∑ s, ((A i p * A j q) * (A k r * A l s)) * F p q r s

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OneElectronClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of the physical one-electron estimate to the full spinful weak-H1
form domain. The only approximation input is the published H=W density result. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def oneElectronOrbitalLp (φ : Position → ℝ) (hφ : MemLp φ 2) :
    Lp ℂ 2 (volume : Measure (Configuration 1)) :=
  (hφ.ofReal.comp_measurePreserving oneElectronCoordinates.measurePreserving).toLp
    (fun x => (φ (oneElectronCoordinates x) : ℂ))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_WeakH1Laplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weak kinetic pairing with a C2 orbital only requires its Laplacian,
not each second partial separately, to belong to L2. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

def configurationRealPartial {n : ℕ} (φ : Configuration n → ℝ)
    (a : Fin n × Fin 3) (x : Configuration n) : ℝ :=
  fderiv ℝ φ x (EuclideanSpace.single a 1)

def configurationRealLaplacian {n : ℕ} (φ : Configuration n → ℝ)
    (x : Configuration n) : ℝ :=
  ∑ a, configurationRealPartial (configurationRealPartial φ a) a x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteOrbitalLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite linear combinations commute with the actual weak-form coordinate
Laplacian. These identities are used only for Gram-corrected orbitals. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem configurationRealPartial_sum {m : ℕ} (c : Fin m → ℝ)
    (f : Fin m → Configuration 1 → ℝ) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (a : Fin 1 × Fin 3) (x : Configuration 1) :
    configurationRealPartial (fun y => ∑ j, c j*f j y) a x =
      ∑ j, c j*configurationRealPartial (f j) a x := by
  unfold configurationRealPartial
  have hd (j : Fin m) := (hf j).differentiable (by norm_num) x
  rw [fderiv_fun_sum (fun j _ => (hd j).const_mul (c j))]
  simp only [sum_apply,fderiv_const_mul (hd _),smul_apply,smul_eq_mul]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RealSpinOrbitals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin lifting of real C1 orbitals into the actual fermionic weak-H1
domain. Any injective list of occupied orthonormal spatial/spin modes
gives a normalized antisymmetric state on the full configuration space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def realSpinOrbital (f : Position → ℝ) (σ : Fin 2) (x : Position) (s : Fin 2) : ℂ :=
  if s = σ then (f x : ℂ) else 0

theorem realSpinOrbital_C1 (f : Position → ℝ) (hf : ContDiff ℝ 1 f) (σ s : Fin 2) :
    ContDiff ℝ 1 (fun x => realSpinOrbital f σ x s) := by
  by_cases h : s = σ
  · simpa only [realSpinOrbital, h, ite_true, if_true, Function.comp_def, Complex.ofRealCLM_apply] using Complex.ofRealCLM.contDiff.comp hf
  · simpa only [realSpinOrbital, h, ite_false, if_false] using (contDiff_const : ContDiff ℝ 1 (fun _ : Position => (0 : ℂ)))

theorem realSpinOrbital_memLp (f : Position → ℝ) (hf : MemLp f 2) (σ s : Fin 2) :
    MemLp (fun x => realSpinOrbital f σ x s) 2 := by
  by_cases h : s = σ
  · simp only [realSpinOrbital, h, ite_true, if_true]
    exact hf.ofReal
  · simp only [realSpinOrbital, h, ite_false, if_false]
    exact MemLp.zero

theorem realSpinOrbital_fderiv (f : Position → ℝ) (hf : ContDiff ℝ 1 f)
    (σ s : Fin 2) (x e : Position) :
    fderiv ℝ (fun y => realSpinOrbital f σ y s) x e =
      if s = σ then (fderiv ℝ f x e : ℂ) else 0 := by
  by_cases h : s = σ
  · simp only [realSpinOrbital, h, ite_true, if_true]
    exact congrArg (fun L : Position →L[ℝ] ℂ => L e)
      (Complex.ofRealCLM.hasFDerivAt.comp x (hf.differentiable (by norm_num) x).hasFDerivAt).fderiv
  · simp [realSpinOrbital, h]

theorem realSpinOrbital_partial_memLp (f : Position → ℝ) (hf : ContDiff ℝ 1 f)
    (hd : ∀ b : Fin 3, MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single b 1)) 2)
    (σ s : Fin 2) (b : Fin 3) :
    MemLp (fun x => fderiv ℝ (fun y => realSpinOrbital f σ y s) x (EuclideanSpace.single b 1)) 2 := by
  simp_rw [realSpinOrbital_fderiv f hf]
  by_cases h : s = σ
  · simp only [h, ite_true, if_true]
    exact (hd b).ofReal
  · simp only [h, ite_false, if_false]
    exact MemLp.zero

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

/-- A nonsingular Coulomb line section, with the other two squared
coordinates (and optional regularization) collected in `A`. -/
def coulombLineKernel (A t : ℝ) : ℝ := (Real.sqrt (A+t^2))⁻¹

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite product sections of the actual rectangular slab measure. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace ContinuumCoulomb

def slabSide (H S : ℝ) (i : Fin 3) : ℝ := if i = 2 then S else H

def slabAxisMeasure (H S : ℝ) (i : Fin 3) : Measure ℝ :=
  volume.restrict (Set.Icc (-slabSide H S i) (slabSide H S i))

def slabProductMeasure (H S : ℝ) : Measure (Fin 3 → ℝ) :=
  Measure.pi (slabAxisMeasure H S)

def slabProductDomain (H S : ℝ) : Set (Fin 3 → ℝ) :=
  Set.univ.pi (fun i => Set.Icc (-slabSide H S i) (slabSide H S i))

instance slabAxisMeasure_finite (H S : ℝ) (i : Fin 3) :
    IsFiniteMeasure (slabAxisMeasure H S i) := by
  unfold slabAxisMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def zeroPositionCoordinate (i : Fin 3) (y : Position) : Position :=
  WithLp.toLp 2 (Function.update (WithLp.ofLp y) i 0)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabPlanarIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact horizontal-plane Coulomb differences. The individually divergent
plane integrals are never separated; their integrable difference has a
finite antiderivative and a zero limit at infinity. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

def slabRootDifference (A B r : ℝ) : ℝ :=
  Real.sqrt (r^2+A) - Real.sqrt (r^2+B)

def slabRadialDifference (A B r : ℝ) : ℝ :=
  r*(coulombLineKernel A r-coulombLineKernel B r)

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

def slabRadialTail (H r : ℝ) : ℝ :=
  (Set.Ioi H).indicator (fun t : ℝ => t ^ (-3 : ℝ)) r

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative removal of the vertical regularization. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

def slabRegularizedProfile (epsilon S z : ℝ) : ℝ :=
  ∫ w in (-S)..S, Real.sqrt (epsilon^2+(z-w)^2)-Real.sqrt (epsilon^2+w^2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_SlabVerticalCoordinates
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

def slabAxisPoint (z : ℝ) : Position := WithLp.toLp 2 ![0,0,z]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoordinateLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate identities for the actual three-dimensional Laplacian. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def directionalSecond {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (e x : E) : ℝ := fderiv ℝ (fun y => fderiv ℝ f y e) x e

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RealOrbitalResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak form of a real one-electron orbital's differential residual.
This is used for finite corrected combinations of the manufactured modes. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def realOrbitalPairing (V : Configuration 1 → ℝ) (E : ℝ)
    (φ : Configuration 1 → ℝ) (v : Coulomb.H1Vector 1) (s : SpinConfiguration 1) : ℂ :=
  (1/2:ℂ)*(∑ a, ∫ x, v.gradient s a x*(configurationRealPartial φ a x : ℂ))+
    (∫ x, v.value s x*(V x*φ x : ℝ))-(E:ℂ)*(∫ x, v.value s x*(φ x : ℂ))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorFirstReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacing one orbital in a finite tensor expansion costs the squared
L2 size of the replacement family, without an exponential dimension factor. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def tensorCoefficientSlice {A ι : Type*} [Fintype ι] {n : ℕ}
    (v : ι → A → ℂ) (c : ι → (Fin n → ι) → ℂ) (a : ι) (y : Fin n → A) : ℂ :=
  ∑ b, c a b*(∏ i, v (b i) (y i))

def tensorFirstReplacement {A ι : Type*} [Fintype ι] {n : ℕ}
    (v r : ι → A → ℂ) (c : ι → (Fin n → ι) → ℂ) (z : (Fin n → A) × A) : ℂ :=
  ∑ a, tensorCoefficientSlice v c a z.1*r a z.2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorSlotReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residual in any electron coordinate has the same polynomial bound.
The regrouping is an exact measure-preserving separation of that coordinate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def tensorSlotReplacement {A ι : Type*} [Fintype ι] {n : ℕ}
    (v r : ι → A → ℂ) (c : (Fin n → ι) → ℂ) (i : Fin n) (x : Fin n → A) : ℂ :=
  ∑ b, c b * ∏ j, if j=i then r (b j) (x j) else v (b j) (x j)

def separateTensorSlot {A : Type*} [MeasurableSpace A] {n : ℕ}
    (i : Fin (n+1)) : (Fin (n+1) → A) ≃ᵐ (Fin n → A) × A :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => A) i).trans MeasurableEquiv.prodComm

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorTotalReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing one-body residuals over electron coordinates costs only the square
of the electron count, even though the tensor coefficient space is exponential. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def tensorTotalReplacement {A ι : Type*} [Fintype ι] {n : ℕ}
    (v r : ι → A → ℂ) (c : (Fin n → ι) → ℂ) (x : Fin n → A) : ℂ :=
  ∑ i, tensorSlotReplacement v r c i x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_WeakComplexLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration by parts for a complex C2 orbital against the full weak-H1
space. Only the sum of its second derivatives is required to lie in L2. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

def configurationComplexPartial {n : ℕ} (φ : Configuration n → ℂ)
    (a : Fin n × Fin 3) (x : Configuration n) : ℂ :=
  fderiv ℝ φ x (EuclideanSpace.single a 1)

def configurationComplexLaplacian {n : ℕ} (φ : Configuration n → ℂ)
    (x : Configuration n) : ℂ :=
  ∑ a, configurationComplexPartial (configurationComplexPartial φ a) a x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate derivatives of tensor products. Cross-coordinate
factors remain constant when differentiating a second time in one slot. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

def coordinateProduct {n : ℕ} (f : Fin n → Position → ℂ) (x : Configuration n) : ℂ :=
  ∏ i, f i (Coulomb.position x i)

def positionComplexPartial (f : Position → ℂ) (b : Fin 3) (x : Position) : ℂ :=
  fderiv ℝ f x (EuclideanSpace.single b 1)

def positionComplexLaplacian (f : Position → ℂ) (x : Position) : ℂ :=
  ∑ b, positionComplexPartial (fun y => positionComplexPartial f b y) b x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_TensorOperatorResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The differential one-body residual of a product is the sum of the
one-orbital residuals in its electron slots. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

def tensorOrbitalResidual {n : ℕ} {α : Type*}
    (v r : α → Position → Fin 2 → ℂ) (b : Fin n → α)
    (s : SpinConfiguration n) (x : Configuration n) : ℂ :=
  ∑ i, r (b i) (Coulomb.position x i) (s i)*
    ∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_LastTensorFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving the contracted electron from the first to the last coordinate
preserves occupation for an antisymmetric full-product wave function. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def lastTensorFiber {A : Type*} {n : ℕ} (f : (Fin (n+1) → A) → ℂ)
    (z : (Fin n → A) × A) : ℂ := f (Fin.snoc z.1 z.2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoreTensorFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The last-coordinate contraction in full spin space is exactly the
core-slice orbital coefficient used by the many-electron energy bound. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def spinConfigurationPoint {n : ℕ} (s : SpinConfiguration n) (x : Configuration n) :
    Fin n → Fin 2 × (Fin 3 → ℝ) := fun i => (s i,fun a => x (i,a))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteTensorResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial tensor residual is the actual differential residual of
finite tensor synthesis in the full physical spin space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def finiteTensorResidualValue {n : ℕ} {α : Type*} [Fintype α]
    (v r : α → Position → Fin 2 → ℂ) (c : (Fin n → α) → ℂ)
    (s : SpinConfiguration n) (x : Configuration n) : ℂ :=
  ∑ b, c b*tensorOrbitalResidual v r b s x

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.Laughlin_Operators_NormalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

noncomputable def delta {Q : ℕ} (i j : Fin (Q+1)) : ℂ := if i = j then 1 else 0

end Laughlin.Fock

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

/-- The spin-`1/2` isotropic Heisenberg matrix in the computational basis. -/
def heisenberg : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, -1, 2, 0;
     0, 2, -1, 0;
     0, 0, 0, 1]

/-- The unnormalized singlet, of squared norm two. -/
def spinSinglet : Fin 4 → ℂ := ![0, 1, -1, 0]

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_WeightedNuclearCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute nuclear form errors control mixed terms on the full complex,
spinful weak-H1 domain. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def nuclearErrorCross {n : ℕ} (F : Position → ℝ) (u v : Coulomb.H1Vector n) : ℝ :=
  ∑ s, ∑ i, ∫ x, F (Coulomb.position x i)*inner ℝ (u.value s x) (v.value s x)

def nuclearAbsoluteError {n : ℕ} (F : Position → ℝ) (u : Coulomb.H1Vector n) : ℝ :=
  ∑ s, ∑ i, ∫ x, |F (Coulomb.position x i)| * ‖u.value s x‖^2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_WeightedNuclearForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polarization and graph bounds for the actual nuclear error potential,
including its Coulomb singularities. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def nuclearErrorEnergy {n : ℕ} (F : Position → ℝ) (u : Coulomb.H1Vector n) : ℝ :=
  ∑ s, ∑ i, ∫ x, F (Coulomb.position x i)*‖u.value s x‖^2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_RepulsionBound
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

def pairRepulsionTerm {n : ℕ} (p : Fin n × Fin n) (x : Configuration n) : ℝ :=
  if p.1 < p.2 then Coulomb.coulombKernel (Coulomb.position x p.1 - Coulomb.position x p.2)
    else 0

def repulsionPotential {n : ℕ} (x : Configuration n) : ℝ :=
  ∑ p : Fin n × Fin n, pairRepulsionTerm p x

theorem repulsionPotential_square_bound {n : ℕ} (x : Configuration n) :
    repulsionPotential x ^ 2 ≤ (n : ℝ) ^ 2 *
      ∑ p : Fin n × Fin n, pairRepulsionTerm p x ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun p => pairRepulsionTerm p x) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul] at h
  change (∑ p, pairRepulsionTerm p x) ^ 2 ≤ _
  nlinarith [h]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_PairTensorCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full-spin Coulomb pair form is exactly the quartic CAR operator
on the finite orbital tensor. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def flatPairCoulomb (x y : Fin 2 × (Fin 3 → ℝ)) : ℂ :=
  (Coulomb.coulombKernel (WithLp.toLp 2 x.2-WithLp.toLp 2 y.2):ℂ)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteTensorFormCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact compression of the interacting continuum form, including the
singular nuclear term, to the actual finite CAR Hamiltonian. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def flatResidualMatrix {Q : ℕ} (v r : Fin (Q+1) → Position → Fin 2 → ℂ)
    (a b : Fin (Q+1)) : ℂ :=
  ∫ z, star (Coulomb.flatSpinOrbital (v a) z)*Coulomb.flatSpinOrbital (r b) z
    ∂Coulomb.spinSpaceMeasure

def flatNuclearMatrix {Q : ℕ} (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (F : Position → ℝ) (a b : Fin (Q+1)) : ℂ :=
  ∫ z, (F (WithLp.toLp 2 z.2):ℂ)*
    (star (Coulomb.flatSpinOrbital (v a) z)*Coulomb.flatSpinOrbital (v b) z)
    ∂Coulomb.spinSpaceMeasure

def flatCoulombTensor {Q : ℕ} (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (a b c d : Fin (Q+1)) : ℂ :=
  ∫ z, flatPairCoulomb z.1 z.2*
    ((star (Coulomb.flatSpinOrbital (v a) z.1)*Coulomb.flatSpinOrbital (v c) z.1)*
      (star (Coulomb.flatSpinOrbital (v b) z.2)*Coulomb.flatSpinOrbital (v d) z.2))
    ∂(Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_FiniteTensorFormError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite continuum form inherits the polynomial CAR coefficient
error bound, with no dependence on the exponentially large Fock dimension. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def nuclearFormIntegrable {n : ℕ} (F : Position → ℝ) (p : Coulomb.H1Vector n) : Prop :=
  ∀ s i, Integrable (fun x => F (Coulomb.position x i)*‖p.value s x‖^2)

end ContinuumCoulomb

end

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

/-- Matrix element in the singlet of squared norm two. -/
def singletMatrixElement (A : Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  ∑ i, star (spinSinglet i) * (A *ᵥ spinSinglet) i

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

def mediatorMemberSign (member : Fin 2) : ℂ := if member = 0 then 1 else -1

def signedMediatorMember (J : ℝ) : Fin 2 := if J < 0 then 0 else 1

def signedMediatorAmplitude (Delta J : ℝ) : ℝ := Real.sqrt (2 * Delta * |J|)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_PairSpinOrbitals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin selection rules for the actual Coulomb four-index integral. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def realPairIntegrand (f g h k : Position → ℝ) (σ τ κ χ : Fin 2)
    (z : (Fin 2 × (Fin 3 → ℝ)) × (Fin 2 × (Fin 3 → ℝ))) : ℂ :=
  flatPairCoulomb z.1 z.2*
    ((star (Coulomb.flatSpinOrbital (realSpinOrbital f σ) z.1)*
      Coulomb.flatSpinOrbital (realSpinOrbital h κ) z.1)*
    (star (Coulomb.flatSpinOrbital (realSpinOrbital g τ) z.2)*
      Coulomb.flatSpinOrbital (realSpinOrbital k χ) z.2))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_FlowMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinates of the actual spatial derivative in the standard orthonormal
basis, preserving its determinant and identifying the divergence with trace. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def flowMatrix (L : Position →L[ℝ] Position) : Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis L.toLinearMap

def flowCoordinate (a : Fin 3) : Position →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) a

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_Dilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spatial dilation on the actual weak H¹ domain

The physical-energy amplification in both manuscripts changes coordinates
on the full fermionic form domain. Here weak derivatives are transformed
by changing variables in the compact-test identity, rather than assuming
pointwise differentiability of an arbitrary state.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem memLp_comp_dilation {n : ℕ} {f : Configuration n → ℂ}
    (hf : MemLp f 2) {scale : ℝ} (hscale : scale ≠ 0) :
    MemLp (fun x => f (scale • x)) 2 := by
  have hm : MemLp f 2 (Measure.map (fun x => scale • x) volume) := by
    rw [Measure.map_addHaar_smul volume hscale]
    exact hf.smul_measure (by simp)
  exact hm.comp_of_map (measurable_const_smul scale).aemeasurable

theorem weak_partial_dilation {n : ℕ} (u g : Configuration n → ℂ)
    (a : Fin n × Fin 3) {scale : ℝ} (hscale : scale ≠ 0)
    (hweak : ∀ (phi : Configuration n → ℝ), ContDiff ℝ (⊤ : ℕ∞) phi →
      HasCompactSupport phi →
      (∫ x, u x * (fderiv ℝ phi x (EuclideanSpace.single a 1) : ℂ)) =
        -(∫ x, g x * (phi x : ℂ)))
    (phi : Configuration n → ℝ) (hphi : ContDiff ℝ (⊤ : ℕ∞) phi)
    (hcompact : HasCompactSupport phi) :
    (∫ x, u (scale • x) * (fderiv ℝ phi x (EuclideanSpace.single a 1) : ℂ)) =
      -(∫ x, (scale : ℂ) * g (scale • x) * (phi x : ℂ)) := by
  let test : Configuration n → ℝ := fun y => phi (scale⁻¹ • y)
  have htest : ContDiff ℝ (⊤ : ℕ∞) test := by dsimp [test]; fun_prop
  have hderiv (y : Configuration n) :
      fderiv ℝ test y (EuclideanSpace.single a 1) =
        scale⁻¹ * fderiv ℝ phi (scale⁻¹ • y) (EuclideanSpace.single a 1) := by
    have hlin : HasFDerivAt (fun z : Configuration n => scale⁻¹ • z)
        (scale⁻¹ • ContinuousLinearMap.id ℝ (Configuration n)) y :=
      (hasFDerivAt_id y).const_smul scale⁻¹
    have h := (hphi.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y hlin
    change fderiv ℝ (phi ∘ fun z => scale⁻¹ • z) y _ = _
    rw [h.fderiv]
    simp
  have hw := hweak test htest (hcompact.comp_smul (inv_ne_zero hscale))
  have hleft : (∫ y, u y * (fderiv ℝ test y (EuclideanSpace.single a 1) : ℂ)) =
      (scale⁻¹ : ℂ) * ∫ y, u y *
        (fderiv ℝ phi (scale⁻¹ • y) (EuclideanSpace.single a 1) : ℂ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp only
      rw [hderiv]
      push_cast
      ring
  rw [hleft] at hw
  have hsC : (scale : ℂ) ≠ 0 := by exact_mod_cast hscale
  have hwscaled := congrArg (fun z : ℂ => (scale : ℂ) * z) hw
  simp only [← mul_assoc, mul_inv_cancel₀ hsC, one_mul] at hwscaled
  let jacobian : ℝ := |(scale ^ Module.finrank ℝ (Configuration n))⁻¹|
  have hchangeLeft :
      (∫ x, u (scale • x) * (fderiv ℝ phi x (EuclideanSpace.single a 1) : ℂ)) =
        jacobian • ∫ y, u y *
          (fderiv ℝ phi (scale⁻¹ • y) (EuclideanSpace.single a 1) : ℂ) := by
    simpa only [inv_smul_smul₀ hscale] using Measure.integral_comp_smul volume
      (fun y => u y * (fderiv ℝ phi (scale⁻¹ • y) (EuclideanSpace.single a 1) : ℂ)) scale
  have hchangeRight : (∫ x, g (scale • x) * (phi x : ℂ)) =
      jacobian • ∫ y, g y * (test y : ℂ) := by
    simpa only [test, inv_smul_smul₀ hscale] using Measure.integral_comp_smul volume
      (fun y => g y * (phi (scale⁻¹ • y) : ℂ)) scale
  have hright : (∫ x, (scale : ℂ) * g (scale • x) * (phi x : ℂ)) =
      (scale : ℂ) * (jacobian • ∫ y, g y * (test y : ℂ)) := by
    calc
      _ = (scale : ℂ) * ∫ x, g (scale • x) * (phi x : ℂ) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun _ => by ring
      _ = _ := by rw [hchangeRight]
  rw [hchangeLeft, hright, hwscaled]
  simp only [Complex.real_smul]
  ring

def dilateState {n : ℕ} (state : Coulomb.H1Vector n) (scale : ℝ) (hscale : scale ≠ 0) :
    Coulomb.H1Vector n where
  value spin x := state.value spin (scale • x)
  gradient spin a x := (scale : ℂ) * state.gradient spin a (scale • x)
  value_L2 spin := memLp_comp_dilation (state.value_L2 spin) hscale
  partial_L2 spin a := (memLp_comp_dilation (state.partial_L2 spin a) hscale).const_mul _
  weak_partial spin a := weak_partial_dilation (state.value spin) (state.gradient spin a)
    a hscale (state.weak_partial spin a)

/-- The Jacobian factor makes spatial dilation preserve the physical norm. -/
def normalizedDilation {n : ℕ} (state : Coulomb.H1Vector n)
    (scale : ℝ) (hscale : scale ≠ 0) : Coulomb.H1Vector n :=
  (dilateState state scale hscale).rsmul
    (Real.sqrt |scale ^ Module.finrank ℝ (Configuration n)|)

/-- Rescaling the nuclear positions leaves all nuclear charges unchanged. -/
def dilatedNuclei {M : ℕ} (S : Coulomb.Nuclei M) (scale : ℝ)
    (hscale : scale ≠ 0) : Coulomb.Nuclei M where
  nonempty := S.nonempty
  position a := scale⁻¹ • S.position a
  distinct := by
    intro a b hab
    apply S.distinct
    have h := congrArg (fun x : Position => scale • x) hab
    simpa only [smul_inv_smul₀ hscale] using h
  charge := S.charge
  charge_ge_one := S.charge_ge_one

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_GaussPositionCell
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

def cubePoint (b : Position) (d x y z : ℝ) : Position :=
  b + x • (d • EuclideanSpace.single 0 1) +
    y • (d • EuclideanSpace.single 1 1) + z • (d • EuclideanSpace.single 2 1)

def positionCellIntegral (b : Position) (h : ℝ) (f : Position → ℝ) : ℝ :=
  (h/2)^3 * (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1,
    f (cubePoint b (h/2) x y z))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_GaussEightNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify tensor quadrature with the actual eight equal point masses and
with the already separated Gauss lattice used by the nuclear construction. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def gaussNodeTriple : (Fin 3 → Fin 2) ≃ Fin 2 × Fin 2 × Fin 2 where
  toFun v := (v 0,v 1,v 2)
  invFun p := ![p.1,p.2.1,p.2.2]
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv p := rfl

def gaussCellCenter (h : ℝ) (k : Fin 3 → ℤ) : Position :=
  WithLp.toLp 2 (fun i => h*(k i:ℝ))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_GaussLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local versions of tensor cubature: regularity is only needed on the
integration cube, which may be far from a Coulomb singularity. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def unitClamp (x : ℝ) : ℝ := max (-1) (min 1 x)

def unitCube3 : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc (-1:ℝ) 1 ∧ p.2.1 ∈ Set.Icc (-1:ℝ) 1 ∧ p.2.2 ∈ Set.Icc (-1:ℝ) 1}


end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_NuclearCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One fixed smooth cutoff supplies all translated and scaled near-nucleus
Hardy estimates; its constants are independent of the mesh and particle count. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

def nuclearBump : ContDiffBump (0 : Position) := ⟨1,2,by norm_num,by norm_num⟩

def nuclearCutoff {n : ℕ} (r : ℝ) (a : Position) (i : Fin n) (x : Configuration n) : ℝ :=
  nuclearBump (r⁻¹ • (Coulomb.position x i-a))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Nuclei_NuclearNearEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The singular near-node term has a localized form bound uniform over all
weak-H1 states. No smoothness of the state or orbital restriction is imposed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def electronBall {n : ℕ} (i : Fin n) (a : Position) (r : ℝ) : Set (Configuration n) :=
  {x | ‖Coulomb.position x i-a‖ ≤ r}

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ComplexMollification
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

theorem re_memLp {n : ℕ} {u : Configuration n → ℂ} (hu : MemLp u 2) :
    MemLp (fun x => (u x).re) 2 := Complex.reCLM.comp_memLp' hu

theorem im_memLp {n : ℕ} {u : Configuration n → ℂ} (hu : MemLp u 2) :
    MemLp (fun x => (u x).im) 2 := Complex.imCLM.comp_memLp' hu

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

def contactLengthTolerance : ℝ := 1 / 100000000

def contactHeightLow (c : ℝ) : ℝ := Real.sqrt (1 - (c + 1 / 1000) ^ 2)
def contactHeightHigh (c : ℝ) : ℝ := Real.sqrt (1 - (c - 1 / 1000) ^ 2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactExtent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The contact realization preserves polynomial coordinate extent. -/

noncomputable section
namespace ContinuumCoulomb

def contactGridAxis (a : ℤ × ℤ) (i : Fin 2) : ℤ := ![a.1, a.2] i

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombBox
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

def coulombNumericalBox (L : ℝ) : Set Position :=
  ⋂ i : Fin 3, {x : Position | |x i| ≤ L}

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombCubeCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Lebesgue coordinates for the two-particle finite Coulomb box. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def twoParticleCoordinates : (Fin 6 → ℝ) ≃ᵐ Position × Position :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 ⊕ Fin 3 => ℝ)
    (finSumFinEquiv (m := 3) (n := 3)).symm).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 3 => ℝ)).trans
      ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).prodCongr
        (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombInverseFifth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse-fifth-power tail is integrable in three dimensions, with the
exact inverse-square dependence needed when summing far-cell errors. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def inverseFifthRadial (r : ℝ) : ℝ → ℝ :=
  (Set.Ioi r).indicator (fun t => t^(-5:ℝ))

def inverseFifthTail (r : ℝ) (x : Position) : ℝ := inverseFifthRadial r ‖x‖

end ContinuumCoulomb

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

def positionOpenCube (b : Position) (h : ℝ) : Set Position :=
  WithLp.ofLp ⁻¹' Set.univ.pi (fun i => Set.Ioo (b i-h/2) (b i+h/2))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_GaussianJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform fourth-order bounds for the actual normalized transverse
Gaussian. Polynomial Gaussian moments bound each explicit derivative. -/

noncomputable section
namespace ContinuumCoulomb

def verticalHermiteCoeffs (freq : ℝ) : Fin 5 → Fin 5 → ℝ :=
  ![![1,0,0,0,0],![0,-freq,0,0,0],![-freq,0,freq^2,0,0],
    ![0,3*freq^2,0,-freq^3,0],![3*freq^2,0,-6*freq^3,0,freq^4]]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace LeanBlast.KLS

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def expectation {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  ∫ x, f x ∂μ

def variance {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  ∫ x, (f x - expectation μ f) ^ 2 ∂μ

def dirichletEnergy {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  ∫ x, ‖gradient f x‖ ^ 2 ∂μ

/-- The exact compactly supported smooth real test-function class. -/
def IsTestFunction {n : ℕ} (f : Space n → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Measures_PotentialMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace LeanBlast.KLS

variable {n : ℕ}

def potentialPartition (V : Space n → ℝ) : ℝ :=
  ∫ x, Real.exp (-V x)

def potentialMeasure (V : Space n → ℝ) : Measure (Space n) :=
  volume.tilted (fun x => -V x)

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Stein_SteinHessianDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Matrix
open scoped BigOperators ContDiff

namespace LeanBlast.KLS

def standardBasisVector {n : ℕ} (i : Fin n) : Space n :=
  EuclideanSpace.basisFun (Fin n) ℝ i

def hessianMatrix {n : ℕ} (f : Space n → ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (fderiv ℝ f) x (standardBasisVector i) (standardBasisVector j)

def steinGamma {n : ℕ} (ψ g h : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ a, ∑ b, gradient g x a * (hessianMatrix ψ x)⁻¹ a b * gradient h x b

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Regularization_RegularPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace LeanBlast.KLS

structure IsRegularPotential {n : ℕ} (V : Space n → ℝ) (t t' : ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ V
  lower_pos : 0 < t
  le_upper : t ≤ t'
  lower_bound : ∀ x v : Space n,
    t * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v
  upper_bound : ∀ x v : Space n,
    fderiv ℝ (fderiv ℝ V) x v v ≤ t' * ‖v‖ ^ 2

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Spectral_BrascampLiebMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace LeanBlast.KLS

def blWeight (t a b : ℝ) : ℝ := Real.exp (-t * a - t ^ 2 / 2 * b)

def blWeightDeriv (t a b : ℝ) : ℝ := (-a - t * b) * blWeight t a b

def blWeightSecond (t a b : ℝ) : ℝ := ((a + t * b) ^ 2 - b) * blWeight t a b

section Moments

variable {n : ℕ} (μ : Measure (Space n)) [IsProbabilityMeasure μ]
  (h q : Space n → ℝ)

def blMoment (t : ℝ) : ℝ := ∫ x, blWeight t (h x) (q x) ∂μ
def blMomentDeriv (t : ℝ) : ℝ := ∫ x, blWeightDeriv t (h x) (q x) ∂μ
def blMomentSecond (t : ℝ) : ℝ := ∫ x, blWeightSecond t (h x) (q x) ∂μ
def blLogMoment (t : ℝ) : ℝ := Real.log (blMoment μ h q t)

@[simp] theorem blMoment_zero : blMoment μ h q 0 = 1 := by
  simp [blMoment, blWeight]

omit [IsProbabilityMeasure μ] in
@[simp] theorem blMomentDeriv_zero : blMomentDeriv μ h q 0 = -(∫ x, h x ∂μ) := by
  simp [blMomentDeriv, blWeightDeriv, blWeight, integral_neg]

end Moments

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.KLS_Spectral_BrascampLiebPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Matrix
open scoped BigOperators ContDiff Topology Matrix.Norms.Elementwise

namespace LeanBlast.KLS

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (V h q : E → ℝ)

def blPerturbation (p : ℝ × E) : ℝ := V p.2 + p.1 * h p.2 + p.1 ^ 2 / 2 * q p.2

end Calculus

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_GaussianPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One-dimensional Gaussian Poincare inequality derived from the
Brascamp–Lieb theorem. This is the spectral input needed for the
transverse oscillator; no spectral assertion is assumed here. -/

noncomputable section
open MeasureTheory
open scoped Topology ContDiff
namespace ContinuumCoulomb
open LeanBlast.KLS

def gaussianPotential (freq : ℝ) (x : Space 1) : ℝ := freq*‖x‖^2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_GaussianLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifying the one-dimensional Euclidean Gaussian form with the real
line. This fixes the normalization and derivative constants for the oscillator. -/

noncomputable section
open MeasureTheory
open scoped Topology ContDiff
namespace ContinuumCoulomb
open LeanBlast.KLS

def gaussianLineEquiv : Space 1 ≃ₗᵢ[ℝ] ℝ where
  toLinearEquiv := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toLinearEquiv
  norm_map' x := by
    change ‖x 0‖ = ‖x‖
    have h : ‖x‖^2 = (x 0)^2 := by
      simpa only [Fin.sum_univ_one] using EuclideanSpace.real_norm_sq_eq x
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (x 0),norm_nonneg x,abs_nonneg (x 0)]

@[simp] theorem gaussianLineEquiv_apply (x : Space 1) : gaussianLineEquiv x=x 0 := rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_IsolatedForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isolated-well energy forms on the actual weak H¹ domain

The perturbation bounds here concern the full one-electron form, including
both Coulomb poles and the capped background. They give the shifted relative
form comparison used before constructing isolated eigenfunctions.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def singlePoleEnergy (a : Position) (state : Coulomb.H1Vector 1) : ℝ :=
  ∑ spin, ∫ x, Coulomb.coulombKernel (Coulomb.position x 0 - a) *
    ‖state.value spin x‖ ^ 2

def hydrogenForm (a : Position) (state : Coulomb.H1Vector 1) : ℝ :=
  Coulomb.kinetic state - singlePoleEnergy a state

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OneElectronTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete normalized weak-H¹ trial, independent of all nuclear data. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def oneElectronBump : ContDiffBump (0 : Configuration 1) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def oneElectronBumpState : Coulomb.H1Vector 1 :=
  Coulomb.H1Vector.ofSmoothCompact
    (fun _ x => (oneElectronBump x : ℂ))
    (fun _ => Complex.ofRealCLM.contDiff.comp oneElectronBump.contDiff)
    (fun _ => oneElectronBump.hasCompactSupport.comp_left Complex.ofReal_zero)

def oneElectronTrial : Coulomb.H1Vector 1 :=
  oneElectronBumpState.rsmul (Real.sqrt (Coulomb.mass oneElectronBumpState))⁻¹

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_IsolatedSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Stability of the unrestricted isolated-well variational bottom

All infima range over normalized spinful weak-H¹ states. The estimates use
form comparison and a concrete normalized bump trial; no eigenfunction, attainment, or
spectral oracle is supplied as an assumption.
-/

noncomputable section
namespace ContinuumCoulomb

def oneElectronEnergy (form : Coulomb.H1Vector 1 → ℝ) : EReal :=
  sInf {e | ∃ state : Coulomb.H1Vector 1,
    Coulomb.mass state = 1 ∧ e = (form state : EReal)}

def hydrogenEnergy (a : Position) : EReal := oneElectronEnergy (hydrogenForm a)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ManufacturedFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The frequency evaluated by the literal programs satisfies exactly the
oscillator/slab relation and lies in the uniform spectral-gap regime. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufactured_scale_positive {rho : ℕ} (hrho : 0 < rho)
    {N : ℝ} (hN : 2 ≤ N) (k : ℕ) : 0 < (8/(rho:ℝ))*(N^k)^30 := by
  have hr : (0:ℝ) < rho := by exact_mod_cast hrho
  have hNp : 0 < N := by linarith
  positivity

theorem manufactured_mesh_positive {N : ℝ} (hN : 2 ≤ N) (k : ℕ) :
    0 < 1/(N^k)^10 := by
  have hNp : 0 < N := by linarith
  positivity

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_OrbitalGraphBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform H1 graph bounds for actual orbitals and their removed tails. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def positionGraphSquare (f : Position → ℝ) : ℝ :=
  (∫ x, f x^2)+∑ k : Fin 3, ∫ x, (fderiv ℝ f x (EuclideanSpace.single k 1))^2

end ContinuumCoulomb

end

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

theorem real_one_electron_partial {f : Position → ℝ} (hf : ContDiff ℝ 1 f)
    (a : Fin 1 × Fin 3) (x : Configuration 1) :
    fderiv ℝ (fun y : Configuration 1 => (f (oneElectronCoordinates y) : ℂ)) x
        (EuclideanSpace.single a 1) =
      (fderiv ℝ f (oneElectronCoordinates x) (EuclideanSpace.single a.2 1) : ℂ) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x
    ((hf.differentiable (by norm_num) _).hasFDerivAt.comp x oneElectronCoordinates.toContinuousLinearEquiv.hasFDerivAt)
  have hn : oneElectronCoordinates (EuclideanSpace.single a 1) = EuclideanSpace.single a.2 1 := by
    rcases a with ⟨a,b⟩
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    exact oneElectronCoordinates_single b
  have h := congrArg (fun L : Configuration 1 →L[ℝ] ℂ => L (EuclideanSpace.single a 1)) hd.fderiv
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,
    ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv,hn] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ScalarMollification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact smooth approximation on the real line, including its derivative.
Only the one-dimensional approximation needed by the oscillator is built. -/

noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution ContDiff
namespace ContinuumCoulomb

def scalarMollifier (k : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1/((k:ℝ)+1)
  rOut := 2/((k:ℝ)+1)
  rIn_pos := one_div_pos.mpr (by positivity)
  rIn_lt_rOut := div_lt_div_of_pos_right (by norm_num) (by positivity)

def scalarMollification (f : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  (scalarMollifier k).normed volume ⋆ f

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

def qmaWitnessRestrict (c : QMACircuit) (hc : c.WellFormed)
    (s : SourceSpinBasis (c.work+1)) : SourceSpinBasis c.witness :=
  fun i => s ⟨i.val,lt_of_lt_of_le i.isLt (hc.1.trans (Nat.le_succ _))⟩

def qmaWitnessExtend (c : QMACircuit) (s : SourceSpinBasis c.witness) :
    SourceSpinBasis (c.work+1) :=
  fun i => if h : i.val < c.witness then s ⟨i.val,h⟩ else 0

theorem qmaWitnessRestrict_extend (c : QMACircuit) (hc : c.WellFormed)
    (s : SourceSpinBasis c.witness) :
    qmaWitnessRestrict c hc (qmaWitnessExtend c s) = s := by
  funext i
  simp [qmaWitnessRestrict,qmaWitnessExtend,i.isLt]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite matrix quadratic forms used by the explicit history Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaQuadratic {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (u : ι → ℂ) : ℝ :=
  (star u ⬝ᵥ M.mulVec u).re

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorAncilla
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Occupation coordinates for the parallel qubit mediator gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def qmaAncillaVacuum : κ → Fin 2 := fun _ => 0

def qmaAncillaSingle (e : κ) : κ → Fin 2 := Function.update qmaAncillaVacuum e 1

def qmaAncillaNumber (a : κ → Fin 2) : ℕ := ∑ e, (a e).val

omit [DecidableEq κ] in
@[simp] theorem qmaAncillaNumber_vacuum :
    qmaAncillaNumber (qmaAncillaVacuum (κ := κ)) = 0 := by
  simp [qmaAncillaNumber,qmaAncillaVacuum]

def qmaAncillaOccupation (e : κ) : Matrix (κ → Fin 2) (κ → Fin 2) ℂ :=
  Matrix.diagonal (fun a => if a e = 1 then 1 else 0)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAncillaCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact vacuum-to-one-excitation columns and their compressions.
All matrices retain every original system coordinate. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ α κ : Type*} [Fintype σ]
  [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]

def qmaSliceColumn (a : α) (A : Matrix σ σ ℂ) : Matrix (σ × α) σ ℂ :=
  fun p t => if p.2 = a then A p.1 t else 0

def qmaAncillaColumn (V : κ → Matrix σ σ ℂ) : Matrix (σ × (κ → Fin 2)) σ ℂ :=
  ∑ e, qmaSliceColumn (qmaAncillaSingle e) (V e)

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

def qmaPauliSign (i : Fin 4) : ℂ := if i = 2 then -1 else 1

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

def qmaMediatorOccupations (D : κ → Matrix σ σ ℂ) :
    Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  ∑ e, D e ⊗ₖ qmaAncillaOccupation e

def qmaAncillaDiagonal (w : (κ → Fin 2) → ℂ) :
    Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  1 ⊗ₖ Matrix.diagonal w

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRectangularOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangular Euclidean operators for the actual mediator columns. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace Classical

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

def qmaMatrixOperator (M : Matrix α β ℂ) : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ α :=
  LinearMap.toContinuousLinearMap M.toEuclideanLin

@[simp] theorem qmaMatrixOperator_apply (M : Matrix α β ℂ) (x : EuclideanSpace ℂ β) (a : α) :
    qmaMatrixOperator M x a = ∑ b, M a b*x b := rfl

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

def qmaFourBits (n : Fin 16) : Fin 4 → Fin 2 :=
  ![⟨n.val/8,by have hn := n.isLt; omega⟩,
    ⟨n.val/4%2,by omega⟩,⟨n.val/2%2,by omega⟩,⟨n.val%2,by omega⟩]

def qmaFourIndex (s : Fin 4 → Fin 2) : Fin 16 :=
  ⟨8*(s 0).val+4*(s 1).val+2*(s 2).val+(s 3).val,by
    have h0 := (s 0).isLt
    have h1 := (s 1).isLt
    have h2 := (s 2).isLt
    have h3 := (s 3).isLt
    omega⟩

def qmaFourBasisEquiv : (Fin 4 → Fin 2) ≃ Fin 16 where
  toFun := qmaFourIndex
  invFun := qmaFourBits
  left_inv s := by
    funext i
    have h0 := (s 0).isLt
    have h1 := (s 1).isLt
    have h2 := (s 2).isLt
    have h3 := (s 3).isLt
    fin_cases i <;> apply Fin.ext <;> simp [qmaFourBits,qmaFourIndex] <;> omega
  right_inv n := by
    apply Fin.ext
    have hn := n.isLt
    simp [qmaFourBits,qmaFourIndex]
    omega

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two rational singlet columns spanning the four-spin encoded qubit. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourRaw0 : Fin 16 → ℚ := ![0,0,0,0,0,1,-1,0,0,-1,1,0,0,0,0,0]
def qmaFourRaw1 : Fin 16 → ℚ := ![0,0,0,2,0,-1,-1,0,0,-1,-1,0,2,0,0,0]

def qmaFourRawEncoding : Matrix (Fin 16) (Fin 2) ℚ :=
  fun s b => if b = 0 then qmaFourRaw0 s else qmaFourRaw1 s

def qmaFourRawLogical (i j : Fin 4) : Matrix (Fin 2) (Fin 2) ℚ :=
  if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) then !![-3,0;0,1]
  else if (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3) then !![0,-3;-1,-2]
  else !![0,3;1,-2]

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

def qmaFourProjectionRational : Matrix (Fin 16) (Fin 16) ℚ := fun s t =>
  qmaFourRaw0 s*qmaFourRaw0 t/4+qmaFourRaw1 s*qmaFourRaw1 t/12

def qmaFourWeight (s : Fin 16) : Fin 5 :=
  ⟨s.val/8+s.val/4%2+s.val/2%2+s.val%2,by have hs := s.isLt; omega⟩

def qmaFourSymmetricWeights : Fin 5 → ℚ := ![8,2,4/3,2,8]

def qmaFourSymmetricRational : Matrix (Fin 16) (Fin 16) ℚ := fun s t =>
  if qmaFourWeight s = qmaFourWeight t then qmaFourSymmetricWeights (qmaFourWeight s) else 0

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of the two exact singlet columns. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourRawComplex : Matrix (Fin 16) (Fin 2) ℂ :=
  qmaFourRawEncoding.map (Rat.castHom ℂ)

def qmaFourNormalization : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![1/2,1/(2*(Real.sqrt 3:ℝ))]

def qmaFourEncoding : Matrix (Fin 16) (Fin 2) ℂ := qmaFourRawComplex*qmaFourNormalization

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

def qmaFourSymmetricColumn : Matrix (Fin 16) (Fin 5) ℚ :=
  fun s k => if qmaFourWeight s = k then 1 else 0

def qmaFourSymmetricColumnComplex : Matrix (Fin 16) (Fin 5) ℂ :=
  qmaFourSymmetricColumn.map (Rat.castHom ℂ)

def qmaFourSymmetricDiagonal : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal (fun k => ((qmaFourSymmetricWeights k:ℝ):ℂ))

def qmaFourProjection : Matrix (Fin 16) (Fin 16) ℂ := qmaFourProjectionRational.map (Rat.castHom ℂ)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourLogical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact logical actions of the six physical exchanges in the singlet code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourLogical (i j : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) then !![-3,0;0,1]
  else if (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3) then !![0,-(Real.sqrt 3:ℂ);-(Real.sqrt 3:ℂ),-2]
  else !![0,(Real.sqrt 3:ℂ);(Real.sqrt 3:ℂ),-2]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourSpinTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse rational tables for the four-spin contractions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourSpinTable00 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,-1,1,0,0,0,0,0,0,0,0,0,0,1,-1,0] s
  else ![0,-1,-1,0,2,0,0,0,0,0,0,2,0,-1,-1,0] s

def qmaFourSpinTable01 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,1,-1,0,0,0,0,0,0,0,0,0,0,1,-1,0] s
  else ![0,1,1,0,-2,0,0,0,0,0,0,2,0,-1,-1,0] s

def qmaFourSpinTable02 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,0,0,0,0,1,-1,0,0,1,-1,0,0,0,0,0] s
  else ![0,0,0,2,0,-1,-1,0,0,1,1,0,-2,0,0,0] s

def qmaFourSpinTable10 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,1,-1,0,0,0,0,0,0,0,0,0,0,-1,1,0] s
  else ![0,-1,-1,0,0,0,0,2,2,0,0,0,0,-1,-1,0] s

def qmaFourSpinTable11 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,-1,1,0,0,0,0,0,0,0,0,0,0,-1,1,0] s
  else ![0,1,1,0,0,0,0,2,-2,0,0,0,0,-1,-1,0] s

def qmaFourSpinTable12 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,0,0,0,0,-1,1,0,0,-1,1,0,0,0,0,0] s
  else ![0,0,0,2,0,1,1,0,0,-1,-1,0,-2,0,0,0] s

def qmaFourSpinTable20 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,0,0,0,-1,0,0,1,1,0,0,-1,0,0,0,0] s
  else ![0,2,0,0,-1,0,0,-1,-1,0,0,-1,0,0,2,0] s

def qmaFourSpinTable21 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,0,0,0,1,0,0,1,-1,0,0,-1,0,0,0,0] s
  else ![0,-2,0,0,1,0,0,-1,1,0,0,-1,0,0,2,0] s

def qmaFourSpinTable22 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,0,0,0,0,1,1,0,0,-1,-1,0,0,0,0,0] s
  else ![0,0,0,-2,0,-1,1,0,0,-1,1,0,2,0,0,0] s

def qmaFourSpinTable30 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,0,0,0,1,0,0,-1,-1,0,0,1,0,0,0,0] s
  else ![0,0,2,0,-1,0,0,-1,-1,0,0,-1,0,2,0,0] s

def qmaFourSpinTable31 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,0,0,0,-1,0,0,-1,1,0,0,1,0,0,0,0] s
  else ![0,0,-2,0,1,0,0,-1,1,0,0,-1,0,2,0,0] s

def qmaFourSpinTable32 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,0,0,0,0,-1,-1,0,0,1,1,0,0,0,0,0] s
  else ![0,0,0,-2,0,1,-1,0,0,1,-1,0,2,0,0,0] s

def qmaFourSpinTable (i : Fin 4) (μ : Fin 3) : Matrix (Fin 16) (Fin 2) ℚ :=
  ![![qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02],![qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12],![qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22],![qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]] i μ

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourCorrelationCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational spin correlations in the two-column singlet code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourRawCorrelation (i j : Fin 4) : Matrix (Fin 2) (Fin 2) ℚ :=
  if i = j then Matrix.diagonal ![4,12]
  else (1/3:ℚ) • (Matrix.diagonal ![4,12]*qmaFourRawLogical (min i j) (max i j))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isotropic physical-spin correlations in the normalized singlet code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourCorrelation (i j : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  if i = j then 1 else (1/3:ℂ) • qmaFourLogical (min i j) (max i j)

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

def qmaTensorSuccEquiv (σ : Type*) (n : ℕ) : (Fin (n+1) → σ) ≃ σ × (Fin n → σ) where
  toFun s := (s 0, fun i => s i.succ)
  invFun s := Fin.cases s.1 s.2
  left_inv s := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv s := by cases s; rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourWeighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Factorized real Heisenberg couplings between two four-spin blocks. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

def qmaFourWeightedCorrelation (a : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i, ∑ k, ((a i*a k:ℝ):ℂ) • qmaFourCorrelation i k

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourStencils
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational physical-spin weights giving shifted logical X and Z. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourXWeights (positive : Bool) : Fin 4 → ℝ :=
  if positive then ![11,-1,-13,3] else ![11,-1,3,-13]

def qmaFourZWeights (positive : Bool) : Fin 4 → ℝ :=
  if positive then ![1,-1,0,0] else ![1,1,0,0]

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

def qmaFourAxisWeights (a : Fin 2) (p : Bool) : Fin 4 → ℝ :=
  if a = 0 then qmaFourXWeights p else qmaFourZWeights p
def qmaFourAxisShift (a : Fin 2) (p : Bool) : ℝ :=
  if a = 0 then 400 else if p then 8/3 else 4/3
def qmaFourAxisScale (a : Fin 2) : ℝ := if a = 0 then 128*Real.sqrt 3 else 4/3
def qmaFourAxisSign (p : Bool) : ℝ := if p then 1 else -1

def qmaFourAxisFieldShift (a : Fin 2) (t : ℝ) : ℝ := if a = 0 then 0 else t/2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourCouplingScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Calibration of the physical inter-block strength for either coupling sign. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourCouplingSign (j : ℝ) : Bool := decide (j ≤ 0)

def qmaFourCouplingSize (a b : Fin 2) (j : ℝ) : ℝ :=
  Real.sqrt (8*|j|/(3*qmaFourAxisScale a*qmaFourAxisScale b))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourEffective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual inter-block coupling has the desired second-order X/Z term. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

def qmaFourCouplingFactor (a b : Fin 2) (j : ℝ) : ℝ := (3/8)*(qmaFourCouplingSize a b j)^2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourCounterterm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Internal exchanges cancel the unwanted one-body terms of the simulator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

def qmaFourCounterA (a b : Fin 2) (j : ℝ) : ℝ :=
  qmaFourCouplingFactor a b j*qmaFourAxisScale a*qmaFourAxisShift b (qmaFourCouplingSign j)

def qmaFourCounterB (a b : Fin 2) (j : ℝ) : ℝ :=
  qmaFourCouplingFactor a b j*qmaFourAxisShift a true*
    (qmaFourAxisSign (qmaFourCouplingSign j)*qmaFourAxisScale b)

def qmaFourEnergyOffset (a b : Fin 2) (j : ℝ) : ℝ :=
  qmaFourAxisFieldShift a (qmaFourCounterA a b j)+
    qmaFourAxisFieldShift b (qmaFourCounterB a b j)-
    qmaFourCouplingFactor a b j*qmaFourAxisShift a true*qmaFourAxisShift b (qmaFourCouplingSign j)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact vacuum and complementary projections for the physical qubits. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaMediatorVacuumColumn : Matrix (σ × (κ → Fin 2)) σ ℂ :=
  qmaSliceColumn qmaAncillaVacuum 1

def qmaMediatorHighMatrix : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  qmaAncillaDiagonal (fun a => if a = qmaAncillaVacuum then 0 else 1)

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

def qmaPaddedExcitationNumber (a : κ → Fin 2) : ℕ :=
  if a = qmaAncillaVacuum then 1 else qmaAncillaNumber a

def qmaPaddedWeight (g : ℝ) (p : σ × (κ → Fin 2)) : ℝ :=
  g*qmaPaddedExcitationNumber p.2

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

def qmaMediatorInclusion : EuclideanSpace ℂ σ →L[ℝ] EuclideanSpace ℂ (σ × (κ → Fin 2)) :=
  (qmaMatrixOperator qmaMediatorVacuumColumn).restrictScalars ℝ

def qmaMediatorRestriction : EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ] EuclideanSpace ℂ σ :=
  (qmaMatrixOperator (qmaMediatorVacuumColumn (σ := σ) (κ := κ)).conjTranspose).restrictScalars ℝ

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGadgetCounterterms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact counterterms make the subdivision and three-body Schur
complements equal the intended interactions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaSubdivisionCounter (rJ : ℂ) : Matrix ι ι ℂ :=
  (1+(-rJ/2)^2) • (1 : Matrix ι ι ℂ)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumThirdCounterterm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The third-order series gadget uses only polynomial coefficients.
Its parallel version is controlled by ThirdOrderPerturbation. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaThirdSeriesPair (A B : Matrix ι ι ℂ) (J : ℂ) : Matrix ι ι ℂ :=
  A+(J/2) • B

def qmaThirdSeriesCounter (A B C : Matrix ι ι ℂ) (r J : ℂ) : Matrix ι ι ℂ :=
  r • ((1+(J/2)^2) • (1 : Matrix ι ι ℂ)+J • (A*B))-
    (1+(J/2)^2) • C

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorSeriesMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact simultaneous cancellation for the polynomial third-order gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]

def qmaThirdSeriesLow (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (r : ℂ) (J : κ → ℂ) : Matrix σ σ ℂ :=
  H+∑ e, qmaThirdSeriesCounter (A e) (B e) (C e) r (J e)

def qmaThirdSeriesTarget (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (J : κ → ℂ) : Matrix σ σ ℂ := H+∑ e, J e • (A e*B e*C e)

def qmaThirdMatrix (L : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) (g : ℂ) : Matrix σ σ ℂ :=
  L-g⁻¹ • (∑ e, (V e).conjTranspose*V e)+
    (g⁻¹)^2 • ((∑ e, (V e).conjTranspose*L*V e)+(∑ e, (V e).conjTranspose*D e*V e))

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

def qmaPhysicalPenaltyMatrix (g : ℝ) : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  qmaAncillaDiagonal (fun a => (g*qmaAncillaNumber a : ℝ))

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

def qmaCouplingOperator (V : κ → Matrix σ σ ℂ) :
    EuclideanSpace ℂ σ →L[ℝ] EuclideanSpace ℂ (σ × (κ → Fin 2)) :=
  (qmaMatrixOperator (qmaAncillaColumn V)).restrictScalars ℝ

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

def qmaFourTensorPerturbation (r : ℝ)
    (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) :
    EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16) :=
  r • (qmaMatrixOperator V).restrictScalars ℝ+(qmaMatrixOperator C).restrictScalars ℝ

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

def qmaFourTensorFieldShift (axis : τ → Fin 2) (weight : τ → ℝ) : ℝ :=
  ∑ e, qmaFourAxisFieldShift (axis e) (weight e)

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

def qmaFourTensorFullBudget (t : κ → ℝ) (weight : τ → ℝ) (constant : ℝ) : ℝ :=
  let s := ∑ e, (1+|t e|)
  let c := 1228800*s+7*(∑ e, |weight e|)+|constant|
  1+7056*s+c+(7056*s)^2

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

def qmaFieldEdgeWeight (a : Fin 2) (t : ℝ) (k : Fin 3) : ℝ :=
  if a = 0 then ![t/(2*Real.sqrt 3),-t/(2*Real.sqrt 3),0] k else ![0,0,-t/2] k

def qmaFourExchangeScalar (n : ℕ) (r : ℝ) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) : ℝ :=
  r^2*(n*6)+constant-qmaFourTensorFieldShift axis weight

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

def qmaCrossingAmplitude (R J K : ℝ) : Fin 4 → ℝ := ![R,R,2*R*J,2*R*K]

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

def qmaCrossingWeight (J K : ℝ) : Fin 4 → ℝ := ![1/2,-K,-J,2*J*K]
def qmaCrossingOffset (J K : ℝ) : ℝ := 3/2+3*J^2+3*K^2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial penalty choice for the second-order routing gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Kronecker

def qmaRoutingScale (A B N : ℝ) : ℝ := 16*(A+B+1)^3*N+4*(A+B+1)+1

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

def qmaForkMember : Fin 3 → Fin 2 := ![0,1,1]
def qmaForkAmplitude (R J K : ℝ) : Fin 3 → ℝ := ![R,2*R*J,2*R*K]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial coefficient and operator bounds for parallel degree reduction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

def qmaForkOffset (J K : ℝ) : ℝ := 3/4+3*J^2+3*K^2

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

def qmaCrossingsBaseWeight {r : ℕ} (weight : ν → ℝ) (J K : Fin r → ℝ) :
    ν ⊕ (Fin r × Fin 4) → ℝ := Sum.elim weight (fun p => qmaCrossingWeight (J p.1) (K p.1) p.2)

end ContinuumCoulomb

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

def qmaForksBaseWeight {r : ℕ} (weight : ν → ℝ) (J K : Fin r → ℝ) :
    ν ⊕ Fin r → ℝ := Sum.elim weight (fun e => 2*J e*K e)

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

def qmaPathAmplitude (even : Bool) (R J : ℝ) : Fin 2 → ℝ := ![R,if even then -2*R*J else 2*R*J]

end ContinuumCoulomb

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
open Matrix
open scoped BigOperators Kronecker Classical
variable {ν : Type*} [Fintype ν]

def qmaPathOffset (J : ℝ) : ℝ := 3/4+3*J^2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkInitialMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The private-port initial state is the physical odd-subdivision Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaOriginalSite {n m : ℕ} (left right : Fin m → Fin n) (e : Fin m) : Fin 2 → Fin n :=
  ![left e,right e]

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

def qmaTransferPermutation {n : ℕ} : List (Fin n × Fin n) → Equiv.Perm (Fin n)
  | [] => Equiv.refl _
  | (i,j)::ps => (qmaTransferPermutation ps).trans (Equiv.swap i j)

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

theorem qmaGridRow_ne (rows : ℕ) (r : Fin rows) : r.castSucc ≠ r.succ := by
  intro h
  have hv := congrArg Fin.val h
  simp at hv

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedBasis
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

def qmaPaddedIndex (work extra : ℕ) : Fin ((work+1)+extra) ≃ Fin (work+extra+1) :=
  finCongr (by omega)

def qmaPaddedLeft (work extra : ℕ) (i : Fin (work+1)) : Fin (work+extra+1) :=
  qmaPaddedIndex work extra (Fin.castAdd extra i)

def qmaPaddedRight (work extra : ℕ) (i : Fin extra) : Fin (work+extra+1) :=
  qmaPaddedIndex work extra (Fin.natAdd (work+1) i)

theorem qmaPaddedLeft_injective (work extra : ℕ) : Function.Injective (qmaPaddedLeft work extra) :=
  (qmaPaddedIndex work extra).injective.comp (Fin.castAdd_injective (work+1) extra)

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

@[simp] theorem qmaPaddedLeft_val (work extra : ℕ) (i : Fin (work+1)) :
    (qmaPaddedLeft work extra i).val = i.val := rfl

@[simp] theorem qmaPaddedRight_val (work extra : ℕ) (i : Fin extra) :
    (qmaPaddedRight work extra i).val = work+1+i.val := rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Pauli multiplication, including the scalar phases needed to
replace a YY interaction by commuting real X/Z factors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaPauliProductIndex (a b : Fin 4) : Fin 4 :=
  ![![0,1,2,3],![1,0,3,2],![2,3,0,1],![3,2,1,0]] a b

def qmaPauliProductPhase (a b : Fin 4) : ℂ :=
  ![![1,1,1,1],![1,1,Complex.I,-Complex.I],
    ![1,-Complex.I,1,Complex.I],![1,Complex.I,-Complex.I,1]] a b

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRationalDegreeReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full degree-three reduction has exact rational output coefficients. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaRationalInitialScale {m : ℕ} (J : Fin m → ℚ) (constant N : ℚ) : ℚ :=
  let A := 3*∑ e, (1+2*|J e|)
  let B := |constant|+4*∑ e, (1+|J e|)^2
  16*(A+B+1)^3*N+4*(A+B+1)+1

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

def qmaPhaseFactor (m : Bool) (a : Fin 2) : ℂ :=
  if m = true ∧ a = 1 then -Complex.I else 1

def qmaAncillaPhase (m : κ → Bool) (a : κ → Fin 2) : ℂ := ∏ e, qmaPhaseFactor (m e) (a e)

def qmaPhaseMatrix (m : κ → Bool) : Matrix (κ → Fin 2) (κ → Fin 2) ℂ :=
  Matrix.diagonal (qmaAncillaPhase m)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitPhaseLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rotated mediator couplings are still one-local and have the required
entry parity to keep the physical Hamiltonian real. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def qmaBitZ (e : κ) : Matrix (κ → Fin 2) (κ → Fin 2) ℂ :=
  Matrix.diagonal (fun a => if a e = 1 then -1 else 1)

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

def qmaPhaseLift (m : κ → Bool) : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  (1 : Matrix σ σ ℂ) ⊗ₖ qmaPhaseMatrix m

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitThirdNormBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational polynomial budget for the third-order counterterms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def qmaThirdWeight (j : ℝ) : ℝ := (1+|j|)^2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitThirdFamilyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summed polynomial coefficient bounds for an actual parallel gadget family. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaThirdBudget (b : ℝ) (J : κ → ℝ) : ℝ := 4*(1+b+∑ e, qmaThirdWeight (J e))

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

def qmaSubdivisionLow (H : Matrix σ σ ℂ) (J : κ → ℂ) : Matrix σ σ ℂ :=
  H+∑ e, qmaSubdivisionCounter (J e)

def qmaSubdivisionTarget (H : Matrix σ σ ℂ) (A B : κ → Matrix σ σ ℂ)
    (J : κ → ℂ) : Matrix σ σ ℂ := H+∑ e, J e • (A e*B e)

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

def qmaXZSubdivisionWeight (R j : ℝ) : Fin 4 → ℝ :=
  ![R^2/2+1+(j/2)^2, -R^2/2, R, -R*j/2]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite qubit relabeling preserves the spatial data and the exact Hamiltonian spectrum. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {Q R : Type*} [Fintype Q] [DecidableEq Q] [Fintype R] [DecidableEq R]

def qmaQubitBasisEquiv (e : Q ≃ R) : (R → Fin 2) ≃ (Q → Fin 2) :=
  Equiv.arrowCongr e.symm (Equiv.refl (Fin 2))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_FormStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Stability of the full variational bottom under nuclear rounding

The Hardy estimate is combined with coercivity of the actual Coulomb form.
Consequently rational rounding is controlled on the unrestricted fermionic
ground-energy infimum, without assuming a minimizing eigenvector or an
independent kinetic-energy bound.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ContinuumCoulomb

/-- The same full fermionic bottom for real positions, prior to rationalization. -/
def formGroundEnergy {m : ℕ} (S : Coulomb.Nuclei m) (n : ℕ) : EReal :=
  sInf {e | ∃ state : FormState n,
    normSq state = 1 ∧ e = (Coulomb.form S state.val : EReal)}

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.MinUncut_Search_RawRationalArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
attribute [fun_prop] Computable ComputablePred

namespace MinUncut.Preprocess
variable {α : Type} [Primcodable α]

@[fun_prop] lemma ca_id : Computable (fun a : α=>a) := Computable.id
@[fun_prop] lemma ca_const {β : Type} [Primcodable β] (b : β) : Computable (fun _ : α=>b) := Computable.const b
@[fun_prop] lemma ca_fst {β : Type} [Primcodable β] : Computable (Prod.fst : α × β → α) := Computable.fst
@[fun_prop] lemma ca_snd {β : Type} [Primcodable β] : Computable (Prod.snd : α × β → β) := Computable.snd
@[fun_prop] lemma ca_comp {β γ : Type} [Primcodable β] [Primcodable γ] {g : β → γ} {f : α → β}
    (hg : Computable g) (hf : Computable f) : Computable (fun x=>g (f x)) := hg.comp hf
@[fun_prop] lemma ca_pair {β γ : Type} [Primcodable β] [Primcodable γ] {f : α → β} {g : α → γ}
    (hf : Computable f) (hg : Computable g) : Computable (fun x=>(f x,g x)) := hf.pair hg
@[fun_prop] lemma ca_add {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x+g x) :=
  Primrec.nat_add.to_comp.comp hf hg
@[fun_prop] lemma ca_sub {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x-g x) :=
  Primrec.nat_sub.to_comp.comp hf hg
@[fun_prop] lemma ca_mul {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x*g x) :=
  Primrec.nat_mul.to_comp.comp hf hg
@[fun_prop] lemma ca_div {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x/g x) :=
  Primrec.nat_div.to_comp.comp hf hg
@[fun_prop] lemma ca_mod {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x%g x) :=
  Primrec.nat_mod.to_comp.comp hf hg

@[fun_prop] lemma ca_and {p q : α → Prop} (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred (fun x=>p x ∧ q x) := by
  rcases hp with ⟨dp,hp⟩
  rcases hq with ⟨dq,hq⟩
  apply Computable.computablePred
  exact (Primrec.and.to_comp.comp hp hq).of_eq (by intro x; simp)
@[fun_prop] lemma ca_natLe {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    ComputablePred (fun x=>f x≤g x) :=
  (Primrec.nat_le.computablePred.decide.comp (hf.pair hg)).computablePred
@[fun_prop] lemma ca_natLt {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    ComputablePred (fun x=>f x<g x) :=
  (Primrec.nat_lt.computablePred.decide.comp (hf.pair hg)).computablePred
end MinUncut.Preprocess

end
namespace MinUncut.Preprocess
variable {α β : Type} [Primcodable α] [Primcodable β]

@[fun_prop] lemma ca_range {f : α → ℕ} (hf : Computable f) :
    Computable (fun a=>List.range (f a)) := Primrec.list_range.to_comp.comp hf
@[fun_prop] lemma ca_sum {f : α → List ℕ} (hf : Computable f) :
    Computable (fun a=>(f a).sum) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).to_comp.comp hf

end MinUncut.Preprocess

end OAI
end


