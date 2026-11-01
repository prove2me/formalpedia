-- Prove2me | Definitions.Def_OAIQ092A008
-- name    : OAIQ092A008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T19:53:51.6999+00:00
-- url     : https://prove2.me/theorems/a913eed4-8d47-4206-a789-5137501fc0db
-- title:
--   Definitions bundle OAIQ092A008 of the split of OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 510 declarations of OpenAI's Lean: 387 definitions, 1 inductive type or structure, 1 instance and 121 theorems. The definitions and types are `OAI.ContinuumCoulomb.FiniteSourceBranch.program`, `OAI.ContinuumCoulomb.FiniteSourceBranch.reduction`, `OAI.ContinuumCoulomb.MediatorIteration.firstGraph`, `OAI.ContinuumCoulomb.MediatorIteration.offset`, `OAI.ContinuumCoulomb.MediatorIteration.secondGraph`, `OAI.ContinuumCoulomb.MediatorListProgram.amplitudeProgram`, `OAI.ContinuumCoulomb.MediatorListProgram.bondProgram`, `OAI.ContinuumCoulomb.MediatorListProgram.centralBase`, `OAI.ContinuumCoulomb.MediatorListProgram.centralProgram`, `OAI.ContinuumCoulomb.MediatorListProgram.centralWeight`, `OAI.ContinuumCoulomb.MediatorListProgram.encodedBond`, `OAI.ContinuumCoulomb.MediatorListProgram.encodedBondLeft`, `OAI.ContinuumCoulomb.MediatorListProgram.encodedBondRest`, `OAI.ContinuumCoulomb.MediatorListProgram.encodedBondRight`, `OAI.ContinuumCoulomb.MediatorListProgram.encodedBondTuple`, `OAI.ContinuumCoulomb.MediatorListProgram.encodedBondWeight`, `OAI.ContinuumCoulomb.MediatorListProgram.environment`, `OAI.ContinuumCoulomb.MediatorListProgram.evenProgram`, `OAI.ContinuumCoulomb.MediatorListProgram.gProgram`, `OAI.ContinuumCoulomb.MediatorListProgram.halfProgram`, `OAI.ContinuumCoulomb.MediatorListProgram.indexProgram`, `OAI.ContinuumCoulomb.MediatorListProgram.indexedCode`, `OAI.ContinuumCoulomb.MediatorListProgram.inputCode`, `OAI.ContinuumCoulomb.MediatorListProgram.leftProgram`, `OAI.ContinuumCoulomb.MediatorListProgram.loopBond`, `OAI.ContinuumCoulomb.MediatorListProgram.loopCode`, `OAI.ContinuumCoulomb.MediatorListProgram.loopEdges`, `OAI.ContinuumCoulomb.MediatorListProgram.loopEnvironment`, `OAI.ContinuumCoulomb.MediatorListProgram.loopIndex`, `OAI.ContinuumCoulomb.MediatorListProgram.loopInput`, `OAI.ContinuumCoulomb.MediatorListProgram.loopSpoke`, `OAI.ContinuumCoulomb.MediatorListProgram.nProgram`, `OAI.ContinuumCoulomb.MediatorListProgram.negativeProgram`, `OAI.ContinuumCoulomb.MediatorListProgram.parametersProgram`, `OAI.ContinuumCoulomb.MediatorListProgram.rProgram`, `OAI.ContinuumCoulomb.MediatorListProgram.rightProgram`, `OAI.ContinuumCoulomb.MediatorListProgram.sourceBonds`, `OAI.ContinuumCoulomb.MediatorListProgram.spoke`, `OAI.ContinuumCoulomb.MediatorListProgram.spokeLeftProgram`, `OAI.ContinuumCoulomb.MediatorListProgram.spokeProgram` and 348 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/Computability, lean/OAI/MathematicalPhysics, in whole or in part: `ContinuumCoulomb_ManyBody_FiniteSourceBranch`, `ContinuumCoulomb_ManyBody_MediatorIteration`, `ContinuumCoulomb_OneParticle_PlanarLocalization`, `ContinuumCoulomb_OneParticle_PlanarModeDerivatives`, `ContinuumCoulomb_OneParticle_PlanarModeH1`, `ContinuumCoulomb_OneParticle_PlanarModeProperties`, `ContinuumCoulomb_OneParticle_PlanarProjectionGap`, `ContinuumCoulomb_OneParticle_PlanarSobolev`, `ContinuumCoulomb_OneParticle_PlanarSobolevDuality`, `ContinuumCoulomb_OneParticle_PlanarSpectralInput`, `ContinuumCoulomb_OneParticle_PlanarWellBottom`, `ContinuumCoulomb_OneParticle_PrefactorCalibration`, `ContinuumCoulomb_OneParticle_PrefactorSourceCalibration`, `ContinuumCoulomb_OneParticle_PrefactorSourceContactCorrectness`, `ContinuumCoulomb_Programs_MediatorListProgram`, `ContinuumCoulomb_Programs_MediatorOffsetProgram`, `ContinuumCoulomb_Programs_MediatorProgram`, `ContinuumCoulomb_Programs_MediatorThreeStageProgram`, `ContinuumCoulomb_Programs_PrefactorCalibrationProgram`, `ContinuumCoulomb_Programs_PrefactorSourceContactProgram`, `ContinuumCoulomb_Programs_SourceContactProgram`, `ContinuumCoulomb_Programs_SourceMetadataProgram`, `ContinuumCoulomb_Programs_SourceNormalizationProgram`, `ContinuumCoulomb_Programs_SourcePositiveProgram`, `ContinuumCoulomb_Programs_SourcePrograms`, `ContinuumCoulomb_Quantum_QuantumAdjacentProgram`, `ContinuumCoulomb_Quantum_QuantumAlgebraicHistory`, `ContinuumCoulomb_Quantum_QuantumAlgebraicScalarProgram`, `ContinuumCoulomb_Quantum_QuantumAxisSampleProgram`, `ContinuumCoulomb_Quantum_QuantumBufferedArmProgram`, `ContinuumCoulomb_Quantum_QuantumBufferedBounds`, `ContinuumCoulomb_Quantum_QuantumBufferedEndpointWalk`, `ContinuumCoulomb_Quantum_QuantumBufferedIntersections`, `ContinuumCoulomb_Quantum_QuantumBufferedLanes`, `ContinuumCoulomb_Quantum_QuantumBufferedListProgram`, `ContinuumCoulomb_Quantum_QuantumBufferedPortChain`, `ContinuumCoulomb_Quantum_QuantumBufferedSharedEdge`, `ContinuumCoulomb_Quantum_QuantumBufferedSupport`, `ContinuumCoulomb_Quantum_QuantumCellPathProgram`, `ContinuumCoulomb_Quantum_QuantumCircuitCode`, `ContinuumCoulomb_Quantum_QuantumCorridorSeparation`, `ContinuumCoulomb_Quantum_QuantumCountertermProgram`, `ContinuumCoulomb_Quantum_QuantumCrossingCompiled`, `ContinuumCoulomb_Quantum_QuantumCrossingListActual`, `ContinuumCoulomb_Quantum_QuantumCrossingListBlock`, `ContinuumCoulomb_Quantum_QuantumCrossingListFamily`, `ContinuumCoulomb_Quantum_QuantumCrossingListLayer`, `ContinuumCoulomb_Quantum_QuantumCrossingListMatrix`, `ContinuumCoulomb_Quantum_QuantumCrossingListSupport`, `ContinuumCoulomb_Quantum_QuantumCrossingPacketEnergy`, `ContinuumCoulomb_Quantum_QuantumCrossingPositionProgram`, `ContinuumCoulomb_Quantum_QuantumCrossingPositionRelabel`, `ContinuumCoulomb_Quantum_QuantumCrossingScaleProgram`, `ContinuumCoulomb_Quantum_QuantumCrossingSelectProgram`, `ContinuumCoulomb_Quantum_QuantumCrossingSiteProgram`, `ContinuumCoulomb_Quantum_QuantumCrossingSupportRelabel`, `ContinuumCoulomb_Quantum_QuantumDistributedFamily`, `ContinuumCoulomb_Quantum_QuantumEndpointListProgram`, `ContinuumCoulomb_Quantum_QuantumEndpointPorts`, `ContinuumCoulomb_Quantum_QuantumExchangeLanes`, `ContinuumCoulomb_Quantum_QuantumExchangeSampleProgram`, `ContinuumCoulomb_Quantum_QuantumFieldSample`, `ContinuumCoulomb_Quantum_QuantumFiniteMembership`, `ContinuumCoulomb_Quantum_QuantumFirstUse`, `ContinuumCoulomb_Quantum_QuantumGateCode`, `ContinuumCoulomb_Quantum_QuantumGateLocality`, `ContinuumCoulomb_Quantum_QuantumGridLocality`, `ContinuumCoulomb_Quantum_QuantumInternalHalfSeparation`, `ContinuumCoulomb_Quantum_QuantumLatticeSource`, `ContinuumCoulomb_Quantum_QuantumListPathStep`, `ContinuumCoulomb_Quantum_QuantumLocalFamily`, `ContinuumCoulomb_Quantum_QuantumLocalPropagation`, `ContinuumCoulomb_Quantum_QuantumManhattanListProgram`, `ContinuumCoulomb_Quantum_QuantumMergeEdges`, `ContinuumCoulomb_Quantum_QuantumMergedEndpointPairs`, `ContinuumCoulomb_Quantum_QuantumMergedSupport`, `ContinuumCoulomb_Quantum_QuantumNearestProgram`, `ContinuumCoulomb_Quantum_QuantumOffsetProgram`, `ContinuumCoulomb_Quantum_QuantumOrderedCoefficient`, `ContinuumCoulomb_Quantum_QuantumOrderedModel`, `ContinuumCoulomb_Quantum_QuantumOrderedSupport`, `ContinuumCoulomb_Quantum_QuantumOrderedTable`, `ContinuumCoulomb_Quantum_QuantumPathScaleProgram`, `ContinuumCoulomb_Quantum_QuantumPathTable`, `ContinuumCoulomb_Quantum_QuantumPathVisitCorrectness`, `ContinuumCoulomb_Quantum_QuantumPermittedEndpointAvoidance`, `ContinuumCoulomb_Quantum_QuantumPermittedRouteSeparation`, `ContinuumCoulomb_Quantum_QuantumPhysicalEndpointCover`, `ContinuumCoulomb_Quantum_QuantumPlanarSelectorTransport`, `ContinuumCoulomb_Quantum_QuantumPortChainProgram`, `ContinuumCoulomb_Quantum_QuantumPreparedCircuit`, `ContinuumCoulomb_Quantum_QuantumRationalCrossing`, `ContinuumCoulomb_Quantum_QuantumRawFamilyProgram`, `ContinuumCoulomb_Quantum_QuantumRawProgram`, `ContinuumCoulomb_Quantum_QuantumReferenceEdges`, `ContinuumCoulomb_Quantum_QuantumReferenceLocal`, `ContinuumCoulomb_Quantum_QuantumReferenceModel`, `ContinuumCoulomb_Quantum_QuantumReferenceTerms`, `ContinuumCoulomb_Quantum_QuantumRouteProgram`, `ContinuumCoulomb_Quantum_QuantumRoutingProgram`, `ContinuumCoulomb_Quantum_QuantumRowInsertion`, `ContinuumCoulomb_Quantum_QuantumSelectedRoute`, `ContinuumCoulomb_Quantum_QuantumSpacedListProgram`, `ContinuumCoulomb_Quantum_QuantumSweepCircuit`, `ContinuumCoulomb_Quantum_QuantumSweepIndex`, `ContinuumCoulomb_Quantum_QuantumSweepListProgram`, `ContinuumCoulomb_Quantum_QuantumSweepProgram`, `ContinuumCoulomb_Quantum_QuantumTranslatedInternalSeparation`, `ContinuumCoulomb_Quantum_QuantumUnaryMatrix`, `ContinuumCoulomb_Quantum_QuantumWalkErasureProgram`, `ContinuumCoulomb_Quantum_QuantumWalkSupport`, `ContinuumCoulomb_Reduction_PublishedFlowInput`, `ContinuumCoulomb_Reduction_SourceCoefficientRounding`, `ContinuumCoulomb_Reduction_SourceContactCorrectness`, `ContinuumCoulomb_Reduction_SourceZeroFilter`, `QuantumFactoring_BitStackProcedures`, `QuantumFactoring_BitStackPrograms`, `QuantumFactoring_BitStackUnary`.
--
--   **Imports.** It imports the published bundle `Def_ContinuumCoulombHardness`; the bundles `OAIQ092A004`, `OAIQ092A005` and `OAIQ092A006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ092A010`, `OAIQ092A013`, `OAIQ092A014`, `OAIQ092A015`, `OAIQ092A016` and `OAIQ092A017`; the statements `OAI_ContinuumCoulomb_CalibratedEvaluation_bisect_residual`, `OAI_ContinuumCoulomb_ContactRationalGlobal_edge_error`, `OAI_ContinuumCoulomb_ContactRationalGlobal_local_end`, `OAI_ContinuumCoulomb_ContactRationalGlobal_local_start`, `OAI_ContinuumCoulomb_ContactRationalLocal_near_base`, `OAI_ContinuumCoulomb_ContactRationalLocal_nonedge_separation`, `OAI_ContinuumCoulomb_CoulombPairSum_error`, `OAI.ContinuumCoulomb.PrefactorSourceContactProgram.exists_source_calibration`, `OAI.ContinuumCoulomb.QuantumCrossingPacketEnergy.list_error`, `OAI.ContinuumCoulomb.binary_coulomb_qmaHard_of_two_inputs`, `OAI_ContinuumCoulomb_coulombHoppingTarget_bounds`, `OAI.ContinuumCoulomb.exists_source_unit_reduction_with_planar_gap`, `OAI.ContinuumCoulomb.manufacturedSlab_test_lower`, `OAI.ContinuumCoulomb.manufactured_grid_witness`, `OAI.ContinuumCoulomb.manufactured_polynomial_comparison`, `OAI.ContinuumCoulomb.manufactured_uniform_nuclear_absolute_form`, `OAI_ContinuumCoulomb_qmaXZBlock_polynomial_accuracy` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard_of_two_inputs`; the proofs of `OAI.ContinuumCoulomb.CalibratedEvaluation.scheduled_residual`, `OAI.ContinuumCoulomb.ContactCalibratedGeometry.calibrated_edge_residual`, `OAI_ContinuumCoulomb_ContactRationalGlobal_edge_error`, `OAI_ContinuumCoulomb_ContactRationalGlobal_local_end`, `OAI_ContinuumCoulomb_ContactRationalGlobal_local_start`, `OAI_ContinuumCoulomb_ContactRationalLocal_near_base`, `OAI_ContinuumCoulomb_ContactRationalLocal_nonedge_separation`, `OAI.ContinuumCoulomb.ManufacturedVelocityEvaluation.approximation_error`, `OAI.ContinuumCoulomb.QuantumCrossingPacketEnergy.list_error`, `OAI.ContinuumCoulomb.binary_coulomb_qmaHard`, `OAI_ContinuumCoulomb_coulombHoppingTarget_bounds`, `OAI.ContinuumCoulomb.manufacturedSlab_test_lower`, `OAI.ContinuumCoulomb.manufactured_uniform_nuclear_absolute_form` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`.
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
import Mathlib.Order.Fin.Basic
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
import Definitions.Def_OAIQ092A004
import Definitions.Def_OAIQ092A005
import Definitions.Def_OAIQ092A006

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackPrograms
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

noncomputable instance nodeFintype {K : Type} (p : Program K) : Fintype (Node p) := by
  induction p with
  | skip => exact inferInstanceAs (Fintype Unit)
  | push => exact inferInstanceAs (Fintype Unit)
  | seq p q hp hq => letI := hp; letI := hq; exact inferInstanceAs (Fintype (Node p ⊕ Node q))
  | cases k a b c ha hb hc =>
    letI := ha; letI := hb; letI := hc
    exact inferInstanceAs (Fintype (Unit ⊕ (Node a ⊕ (Node b ⊕ Node c))))
  | loop k b c hb hc =>
    letI := hb; letI := hc
    exact inferInstanceAs (Fintype (Unit ⊕ (Node b ⊕ Node c)))

def statement {K Λ : Type} : (p : Program K) → Λ → (Node p → Λ) → Node p →
    Stmt (fun _ : K => Bool) Λ (Option Bool)
  | .skip,e,_,_ => jump e
  | .push k b,e,_,_ => .push k (fun _ => b) (jump e)
  | .seq p q,_e,w,.inl i => statement p (w (.inr (entry q))) (w ∘ Sum.inl) i
  | .seq _ q,e,w,.inr i => statement q e (w ∘ Sum.inr) i
  | .cases k a b c,_,w,.inl _ => dispatch k
      (w (.inr (.inl (entry a)))) (w (.inr (.inr (.inl (entry b)))))
      (w (.inr (.inr (.inr (entry c)))))
  | .cases _ a _ _,e,w,.inr (.inl i) => statement a e (w ∘ Sum.inr ∘ Sum.inl) i
  | .cases _ _ b _,e,w,.inr (.inr (.inl i)) =>
      statement b e (w ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl) i
  | .cases _ _ _ c,e,w,.inr (.inr (.inr i)) =>
      statement c e (w ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr) i
  | .loop k b c,e,w,.inl _ => dispatch k e
      (w (.inr (.inl (entry b)))) (w (.inr (.inr (entry c))))
  | .loop _ b _,_,w,.inr (.inl i) =>
      statement b (w (.inl ())) (w ∘ Sum.inr ∘ Sum.inl) i
  | .loop _ _ c,_,w,.inr (.inr i) =>
      statement c (w (.inl ())) (w ∘ Sum.inr ∘ Sum.inr) i

lemma dispatch_nil {K Λ : Type} [DecidableEq K] (s : Store K) (k : K) (a b c : Λ)
    (hs : s k=[]) : stepAux (dispatch k a b c) none s = configured a s := by
  simp only [dispatch,stepAux,hs,List.head?_nil,List.tail_nil,Option.isSome_none,
    Bool.cond_false,jump]
  rw [← hs,Function.update_eq_self]
  rfl
lemma dispatch_false {K Λ : Type} [DecidableEq K] (s : Store K) (k : K) (a b c : Λ)
    (xs : List Bool) (hs : s k=false::xs) :
    stepAux (dispatch k a b c) none s = configured b (Function.update s k xs) := by
  simp only [dispatch,stepAux,hs,List.head?_cons,List.tail_cons,Option.isSome_some,
    Bool.cond_true,Option.getD_some,Bool.cond_false,jump]
  rfl
lemma dispatch_true {K Λ : Type} [DecidableEq K] (s : Store K) (k : K) (a b c : Λ)
    (xs : List Bool) (hs : s k=true::xs) :
    stepAux (dispatch k a b c) none s = configured c (Function.update s k xs) := by
  simp only [dispatch,stepAux,hs,List.head?_cons,List.tail_cons,Option.isSome_some,
    Bool.cond_true,Option.getD_some,jump]
  rfl

theorem compile_runs {K : Type} [DecidableEq K] {p : Program K}
    {s t : Store K} {c : ℕ} (h : Runs p s t c) :
    ∀ {Λ : Type} (e : Λ) (w : Node p → Λ)
      (M : Λ → Stmt (fun _ : K => Bool) Λ (Option Bool)),
      (∀ i, M (w i) = statement p e w i) →
      (flip bind (step M))^[c] (some (configured (w (entry p)) s)) = some (configured e t) := by
  induction h with
  | skip s =>
    intro Λ e w M hM
    apply iterate_step
    change some (stepAux (M (w ())) none s) = _
    rw [hM ()]
    rfl
  | push s k b =>
    intro Λ e w M hM
    apply iterate_step
    change some (stepAux (M (w ())) none s) = _
    rw [hM ()]
    rfl
  | @seq p q s t u a b hp hq ihp ihq =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (entry q))) t) _ a b
    · exact ihp _ _ M (fun i => hM (.inl i))
    · exact ihq _ _ M (fun i => hM (.inr i))
  | @cases_nil k p q r s t a hs hp ih =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inl (entry p)))) s) _ 1 a
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_nil _ _ _ _ _ hs]
    · exact ih _ _ M (fun i => hM (.inr (.inl i)))
  | @cases_false k p q r s t xs a hs hp ih =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inr (.inl (entry q)))))
      (Function.update s k xs)) _ 1 a
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_false _ _ _ _ _ _ hs]
    · exact ih _ _ M (fun i => hM (.inr (.inr (.inl i))))
  | @cases_true k p q r s t xs a hs hp ih =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inr (.inr (entry r)))))
      (Function.update s k xs)) _ 1 a
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_true _ _ _ _ _ _ hs]
    · exact ih _ _ M (fun i => hM (.inr (.inr (.inr i))))
  | @loop_nil k p q s hs =>
    intro Λ e w M hM
    apply iterate_step
    change some (stepAux (M (w (.inl ()))) none s) = _
    rw [hM (.inl ()),statement,dispatch_nil _ _ _ _ _ hs]
  | @loop_false k p q s t u xs a b hs hp hq ihp ihq =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inl (entry p))))
      (Function.update s k xs)) _ 1 (b+a)
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_false _ _ _ _ _ _ hs]
    · apply iterate_comp (step M) _ (configured (w (.inl ())) t) _ a b
      · exact ihp _ _ M (fun i => hM (.inr (.inl i)))
      · exact ihq _ _ M hM
  | @loop_true k p q s t u xs a b hs hp hq ihp ihq =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inr (entry q))))
      (Function.update s k xs)) _ 1 (b+a)
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_true _ _ _ _ _ _ hs]
    · apply iterate_comp (step M) _ (configured (w (.inl ())) t) _ a b
      · exact ihp _ _ M (fun i => hM (.inr (.inr i)))
      · exact ihq _ _ M hM

noncomputable def machine {K : Type} [Fintype K] [DecidableEq K] (input output : K) (p : Program K) :
    Turing.FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ _ := Bool
  Λ := Option (Node p)
  main := some (entry p)
  σ := Option Bool
  initialState := none
  m
    | none => .halt
    | some i => statement p none some i

noncomputable def machine_outputs {K : Type} [Fintype K] [DecidableEq K]
    (input output : K) (p : Program K) (s t : List Bool) (c : ℕ)
    (h : Runs p (singletonStore input s) (singletonStore output t) c) :
    Turing.TM2OutputsInTime (machine input output p) s (some t) (c+1) := by
  let tm := machine input output p
  have hi : Turing.initList tm s = configured (some (entry p)) (singletonStore input s) := by
    change Turing.initList (machine input output p) s = _
    unfold machine Turing.initList configured singletonStore
    congr 1
    funext k
    by_cases hk : k=input
    · subst k; simp
    · simp [hk,Function.update]
  have hf : Turing.haltList tm t =
      (⟨none,none,singletonStore output t⟩ : Config K (Option (Node p))) := by
    change Turing.haltList (machine input output p) t = _
    unfold machine Turing.haltList singletonStore
    congr 1
    funext k
    by_cases hk : k=output
    · subst k; simp
    · simp [hk,Function.update]
  have hr := compile_runs h (none : Option (Node p)) some tm.m (fun _ => rfl)
  refine ⟨⟨c+1,?_⟩,le_rfl⟩
  change (flip bind (step tm.m))^[c+1] (some (Turing.initList tm s)) =
    some (Turing.haltList tm t)
  rw [hi,hf]
  have hend : step tm.m (configured (none : Option (Node p)) (singletonStore output t)) =
      some (⟨none,none,singletonStore output t⟩ : Config K (Option (Node p))) := rfl
  rw [Nat.add_comm c 1]
  exact iterate_comp (step tm.m) _ _ _ c 1 hr (iterate_step _ _ _ hend)
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BitStackProcedures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K : Type} [DecidableEq K]

attribute [instance] Procedure.finiteK Procedure.decideK
namespace Procedure
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

noncomputable def toTM2 (p : Procedure ea eb f) : Turing.TM2ComputableInPolyTime ea eb f where
  tm := machine p.input p.output p.program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := p.bound+1
  outputsFun a := by
    classical
    let c := Classical.choose (p.runs a)
    have hc := (Classical.choose_spec (p.runs a)).1
    have hr := (Classical.choose_spec (p.runs a)).2
    have h := machine_outputs p.input p.output p.program (ea a) (eb (f a)) c hr
    have ht : Turing.TM2OutputsInTime (machine p.input p.output p.program)
        (ea a) (some (eb (f a))) (p.bound.eval (ea a).length+1) :=
      ⟨h.1, h.2.trans (Nat.add_le_add_right hc 1)⟩
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Polynomial.eval_add,Polynomial.eval_one]
    congr 1
    · exact List.map_id _
    · congr 1
      exact List.map_id _

end Procedure
end ExactQuantumFactoring.BitStackProgram

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

noncomputable def unarySub : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x=>x.1-x.2) := by
  let p:=unaryPred.iterate Polynomial.X (by
    intro n a i _
    simp only [pred_iterate_word,unaryCode,List.length_replicate,Polynomial.eval_X]
    omega)
  exact (p.comp (swap unaryCode unaryCode)).congrFun (by intro x;simp [pred_iterate_word])

noncomputable def unaryLe : Procedure (prodCode unaryCode unaryCode) boolCode
    (fun x=>decide (x.1≤x.2)) :=
  (unaryZero.comp unarySub).congrFun (by intro x;simp only [Function.comp_apply,decide_eq_decide];omega)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


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

def firstGraph {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2) (r + r * 2) := join (firstCentral F W G) (firstSpokes F W G)

def secondGraph {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2 + r * 2 * 2) (r + (r * 2 + r * 2 * 2)) :=
  join (retainedCentral F W G) (secondPaths F W G)

def offset {n r : ℕ} (F : Bonds n r) (W G : ℕ) : ℚ :=
  (3 * r * deltaOne r W G + 3 * ∑ e, |F.weight e|) +
    (3 * (r * 2) * deltaTwo r W G + 3 * ∑ e, |(firstSpokes F W G).weight e|) +
    (3 * (r * 2 + r * 2 * 2) * deltaThree r W G + 3 * ∑ e, |(secondPaths F W G).weight e|)

end ContinuumCoulomb.MediatorIteration

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_MediatorProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

noncomputable def cubeProgram : Procedure Nat.bits Nat.bits (fun n => n ^ 3) :=
  (Procedure.binaryPow.comp ((Procedure.constant Nat.bits unaryCode 3).pair
    (Procedure.identity Nat.bits))).congrFun (by intro n; rfl)

noncomputable def rCubeProgram : Procedure rawCode Nat.bits (fun x => (x.1 + 1) ^ 3) :=
  (cubeProgram.comp (Procedure.unaryToBits.comp
    (Procedure.unarySuccessor.comp rProgram))).congrFun (by intro x; rfl)

noncomputable def wCubeProgram : Procedure rawCode Nat.bits (fun x => x.2.1 ^ 3) :=
  (cubeProgram.comp (Procedure.unaryToBits.comp wProgram)).congrFun (by intro x; rfl)

noncomputable def cubicProductProgram : Procedure rawCode Nat.bits
    (fun x => (x.1 + 1) ^ 3 * x.2.1 ^ 3) :=
  Procedure.binaryMul.comp (rCubeProgram.pair wCubeProgram)

noncomputable def scaleProgram : Procedure rawCode Nat.bits
    (fun x => MediatorParameters.scale x.1 x.2.1 x.2.2.1) := by
  let product := Procedure.binaryMul.comp
    (cubicProductProgram.pair (Procedure.unaryToBits.comp gProgram))
  exact (Procedure.binaryMul.comp ((Procedure.constant rawCode Nat.bits 1048576).pair
    product)).congrFun (by
      intro x
      simp only [Function.comp_apply, id_eq, MediatorParameters.scale]
      ring)

noncomputable def deltaProgram : Procedure rawCode Nat.bits
    (fun x => MediatorParameters.delta x.1 x.2.1 x.2.2.1) :=
  (mediatorCompBeta Procedure.binaryMul (scaleProgram.pair scaleProgram)).congrFun
    (by intro x; exact (pow_two _).symm)

noncomputable def absoluteProgram : Procedure ratCode ratCode abs :=
  (Procedure.conditional (Procedure.intSign.comp Procedure.ratNum)
    Procedure.ratNeg (Procedure.identity ratCode)).congrFun (by
      intro q
      by_cases hn : q.num < 0
      · have hq : q < 0 := lt_of_not_ge (fun hq => (not_lt_of_ge (Rat.num_nonneg.mpr hq)) hn)
        simp [hn, abs_of_neg hq]
      · have hq : 0 ≤ q := Rat.num_nonneg.mp (le_of_not_gt hn)
        simp [hn, abs_of_nonneg hq])

noncomputable def deltaRationalProgram : Procedure rawCode ratCode
    (fun x => (MediatorParameters.delta x.1 x.2.1 x.2.2.1 : ℚ)) :=
  Procedure.natToRat.comp deltaProgram

noncomputable def radicandProgram : Procedure rawCode ratCode
    (fun x => MediatorParameters.radicand x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let product := Procedure.ratMul.comp (deltaRationalProgram.pair (absoluteProgram.comp jProgram))
  exact (Procedure.ratMul.comp ((Procedure.constant rawCode ratCode 2).pair product)).congrFun
    (by
      intro x
      simp only [Function.comp_apply, MediatorParameters.radicand]
      ring)

noncomputable def numeratorProgram : Procedure rawCode Nat.bits
    (fun x => (MediatorParameters.radicand x.1 x.2.1 x.2.2.1 x.2.2.2).num.toNat) :=
  ChargePrograms.intToNatProgram.comp (Procedure.ratNum.comp radicandProgram)

noncomputable def denominatorProgram : Procedure rawCode Nat.bits
    (fun x => (MediatorParameters.radicand x.1 x.2.1 x.2.2.1 x.2.2.2).den) :=
  Procedure.ratDen.comp radicandProgram

noncomputable def rootInputProgram : Procedure rawCode DyadicRootProgram.rawCode
    (fun x => (MediatorParameters.precision x.1 x.2.2.1,
      (MediatorParameters.radicand x.1 x.2.1 x.2.2.1 x.2.2.2).num.toNat,
      (MediatorParameters.radicand x.1 x.2.1 x.2.2.1 x.2.2.2).den)) :=
  precisionProgram.pair (numeratorProgram.pair denominatorProgram)

noncomputable def spokeProgram : Procedure rawCode ratCode
    (fun x => MediatorParameters.spoke x.1 x.2.1 x.2.2.1 x.2.2.2) :=
  (DyadicRootProgram.rawProgram.comp rootInputProgram).congrFun (by intro x; rfl)

end ContinuumCoulomb.MediatorProgram

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

noncomputable def edgesRaw : Procedure binaryHeisenbergCodec.encode edgeListCodec.encode
    BinaryHeisenberg.edges := (Procedure.first _ _).comp tailTuple

noncomputable def edges : Procedure binaryHeisenbergCodec.encode
    (listCode binaryHeisenbergEdgeCodec.encode) BinaryHeisenberg.edges :=
  (PrefixListPrograms.listInput binaryHeisenbergEdgeCodec edgeSplitter ⟨0, 0, ⟨0, 1⟩⟩ edge_length_pos).comp edgesRaw

end ContinuumCoulomb.SourcePrograms

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_MediatorListProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

def indexedCode : IndexedBond → List Bool := prodCode envCode (prodCode unaryCode bondCode)

noncomputable def environment : Procedure indexedCode envCode Prod.fst := Procedure.first _ _

noncomputable def rProgram : Procedure indexedCode unaryCode (fun x => x.1.1) :=
  (Procedure.first _ _).comp environment

noncomputable def wProgram : Procedure indexedCode unaryCode (fun x => x.1.2.1) :=
  ((Procedure.first _ _).comp (Procedure.second _ _)).comp environment

noncomputable def gProgram : Procedure indexedCode unaryCode (fun x => x.1.2.2.1) :=
  (((Procedure.first _ _).comp (Procedure.second _ _)).comp (Procedure.second _ _)).comp environment

noncomputable def nProgram : Procedure indexedCode unaryCode (fun x => x.1.2.2.2) :=
  (((Procedure.second _ _).comp (Procedure.second _ _)).comp (Procedure.second _ _)).comp environment

noncomputable def indexProgram : Procedure indexedCode Nat.bits (fun x => x.2.1) :=
  Procedure.unaryToBits.comp ((Procedure.first _ _).comp (Procedure.second _ _))

noncomputable def bondProgram : Procedure indexedCode bondCode (fun x => x.2.2) :=
  (Procedure.second _ _).comp (Procedure.second _ _)

noncomputable def leftProgram : Procedure indexedCode Nat.bits (fun x => x.2.2.1) :=
  (Procedure.first _ _).comp bondProgram

noncomputable def rightProgram : Procedure indexedCode Nat.bits (fun x => x.2.2.2.1) :=
  ((Procedure.first _ _).comp (Procedure.second _ _)).comp bondProgram

noncomputable def weightProgram : Procedure indexedCode ratCode (fun x => x.2.2.2.2) :=
  ((Procedure.second _ _).comp (Procedure.second _ _)).comp bondProgram

noncomputable def parametersProgram : Procedure indexedCode MediatorProgram.rawCode
    (fun x => (x.1.1, x.1.2.1, x.1.2.2.1, x.2.2.2.2)) :=
  rProgram.pair (wProgram.pair (gProgram.pair weightProgram))

noncomputable def amplitudeProgram : Procedure indexedCode ratCode
    (fun x => MediatorParameters.spoke x.1.1 x.1.2.1 x.1.2.2.1 x.2.2.2.2) :=
  (MediatorProgram.spokeProgram.comp parametersProgram).congrFun (by intro x; rfl)

noncomputable def halfProgram : Procedure indexedCode Nat.bits (fun x => x.2.1 / 2) :=
  Procedure.binaryDiv.comp (indexProgram.pair (Procedure.constant indexedCode Nat.bits 2))

noncomputable def evenProgram : Procedure indexedCode Procedure.boolCode (fun x => decide (x.2.1 % 2 = 0)) :=
  Procedure.binaryZero.comp (Procedure.binaryMod.comp
    (indexProgram.pair (Procedure.constant indexedCode Nat.bits 2)))

noncomputable def negativeProgram : Procedure indexedCode Procedure.boolCode
    (fun x => decide (x.2.2.2.2 < 0)) :=
  (Procedure.intSign.comp (Procedure.ratNum.comp weightProgram)).congrFun (by
    intro x
    simp only [Function.comp_apply]
    simp only [Rat.num_neg])

noncomputable def spokeLeftProgram : Procedure indexedCode Nat.bits
    (fun x => if x.2.1 % 2 = 0 then x.2.2.1 else x.2.2.2.1) :=
  (Procedure.conditional evenProgram leftProgram rightProgram).congrFun (by intro x; simp)

noncomputable def vertexBaseProgram : Procedure indexedCode Nat.bits
    (fun x => x.1.2.2.2 + 2 * (x.2.1 / 2)) :=
  Procedure.binaryAdd.comp ((Procedure.unaryToBits.comp nProgram).pair
    (Procedure.binaryMul.comp ((Procedure.constant indexedCode Nat.bits 2).pair halfProgram)))

noncomputable def spokeRightProgram : Procedure indexedCode Nat.bits
    (fun x => x.1.2.2.2 + 2 * (x.2.1 / 2) +
      if x.2.1 % 2 = 0 then 0 else if x.2.2.2.2 < 0 then 0 else 1) := by
  let zero := Procedure.constant indexedCode Nat.bits 0
  let one := Procedure.constant indexedCode Nat.bits 1
  let odd := Procedure.conditional negativeProgram zero one
  let member := Procedure.conditional evenProgram zero odd
  exact (Procedure.binaryAdd.comp (vertexBaseProgram.pair member)).congrFun (by intro x; simp)

def spoke (x : IndexedBond) : Bond :=
  (if x.2.1 % 2 = 0 then x.2.2.1 else x.2.2.2.1,
    x.1.2.2.2 + 2 * (x.2.1 / 2) +
      if x.2.1 % 2 = 0 then 0 else if x.2.2.2.2 < 0 then 0 else 1,
    MediatorParameters.spoke x.1.1 x.1.2.1 x.1.2.2.1 x.2.2.2.2)

noncomputable def spokeProgram : Procedure indexedCode bondCode spoke :=
  spokeLeftProgram.pair (spokeRightProgram.pair amplitudeProgram)

def inputCode : Input → List Bool := prodCode envCode (listCode bondCode)

def loopCode : LoopInput → List Bool := prodCode unaryCode inputCode

noncomputable def loopIndex : Procedure loopCode unaryCode Prod.fst := Procedure.first _ _

noncomputable def loopInput : Procedure loopCode inputCode Prod.snd := Procedure.second _ _

noncomputable def loopEnvironment : Procedure loopCode envCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp loopInput

noncomputable def loopEdges : Procedure loopCode (listCode bondCode) (fun x => x.2.2) :=
  (Procedure.second _ _).comp loopInput

noncomputable def loopBond : Procedure loopCode bondCode
    (fun x => (x.2.2.drop (x.1 / 2)).headD zeroBond) :=
  (Procedure.listGet bondCode zeroBond).comp
    ((Procedure.binaryDiv.comp ((Procedure.unaryToBits.comp loopIndex).pair
      (Procedure.constant loopCode Nat.bits 2))).pair loopEdges)

noncomputable def loopSpoke : Procedure loopCode bondCode
    (fun x => spoke (x.2.1, x.1, (x.2.2.drop (x.1 / 2)).headD zeroBond)) :=
  spokeProgram.comp (loopEnvironment.pair (loopIndex.pair loopBond))

def spokes (x : Input) : List Bond := (List.range (2 * x.2.length)).map
  (fun i => spoke (x.1, i, (x.2.drop (i / 2)).headD zeroBond))

noncomputable def spokesProgram : Procedure inputCode (listCode bondCode) spokes := by
  let len : Procedure inputCode unaryCode (fun x => x.2.length) :=
    (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode zeroBond).comp (Procedure.second _ _)
  let twice := Procedure.unaryAdd.comp (len.pair len)
  exact ((Procedure.tabulate (ea := inputCode) (eb := bondCode)
      (f := fun (x : Input) i => spoke (x.1, i, (x.2.drop (i / 2)).headD zeroBond)) zeroBond loopSpoke).comp
    (twice.pair (Procedure.identity inputCode))).congrFun (by intro x; simp only [Function.comp_apply, id_eq, spokes]; congr 2; omega)

noncomputable def centralBase : Procedure loopCode Nat.bits (fun x => x.2.1.2.2.2 + 2 * x.1) := by
  let n := (((Procedure.second unaryCode unaryCode).comp
    (Procedure.second unaryCode (prodCode unaryCode unaryCode))).comp
      (Procedure.second unaryCode (prodCode unaryCode (prodCode unaryCode unaryCode)))).comp loopEnvironment
  exact Procedure.binaryAdd.comp ((Procedure.unaryToBits.comp n).pair
    (Procedure.binaryMul.comp ((Procedure.constant loopCode Nat.bits 2).pair
      (Procedure.unaryToBits.comp loopIndex))))

noncomputable def centralWeight : Procedure loopCode ratCode
    (fun x => (MediatorParameters.delta x.2.1.1 x.2.1.2.1 x.2.1.2.2.1 : ℚ)) := by
  let r : Procedure loopCode unaryCode (fun x => x.2.1.1) :=
    (Procedure.first unaryCode _).comp loopEnvironment
  let rest : Procedure loopCode (prodCode unaryCode (prodCode unaryCode unaryCode))
      (fun x => x.2.1.2) := (Procedure.second unaryCode _).comp loopEnvironment
  let w : Procedure loopCode unaryCode (fun x => x.2.1.2.1) :=
    (Procedure.first unaryCode _).comp rest
  let g : Procedure loopCode unaryCode (fun x => x.2.1.2.2.1) :=
    ((Procedure.first unaryCode unaryCode).comp (Procedure.second unaryCode _)).comp rest
  let params : Procedure loopCode MediatorProgram.rawCode
      (fun x => (x.2.1.1, x.2.1.2.1, x.2.1.2.2.1, 0)) :=
    r.pair (w.pair (g.pair (Procedure.constant loopCode ratCode 0)))
  exact (MediatorProgram.deltaRationalProgram.comp params).congrFun (by intro x; rfl)

noncomputable def centralProgram : Procedure inputCode (listCode bondCode) central := by
  let len : Procedure inputCode unaryCode (fun x => x.2.length) :=
    (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode zeroBond).comp (Procedure.second _ _)
  let edge : Procedure loopCode bondCode (fun x =>
      (x.2.1.2.2.2 + 2 * x.1, x.2.1.2.2.2 + 2 * x.1 + 1,
        (MediatorParameters.delta x.2.1.1 x.2.1.2.1 x.2.1.2.2.1 : ℚ))) :=
    centralBase.pair ((Procedure.successor.comp centralBase).pair centralWeight)
  exact ((Procedure.tabulate (ea := inputCode) (eb := bondCode)
      (f := fun (x : Input) i => (x.1.2.2.2 + 2 * i, x.1.2.2.2 + 2 * i + 1,
        (MediatorParameters.delta x.1.1 x.1.2.1 x.1.2.2.1 : ℚ))) zeroBond edge).comp
    (len.pair (Procedure.identity inputCode))).congrFun (by intro x; rfl)

noncomputable def stageProgram : Procedure inputCode (listCode bondCode)
    (fun x => central x ++ spokes x) :=
  (Procedure.listAppend bondCode zeroBond).comp (centralProgram.pair spokesProgram)

noncomputable def encodedBondTuple : Procedure binaryHeisenbergEdgeCodec.encode
    (prodCode BinaryEncoding.natural.encode
      (BinaryEncoding.pair BinaryEncoding.natural binaryRationalCodec).encode)
    binaryHeisenbergEdgeEquiv :=
  (SourcePrograms.pairInput _ _ PrefixPrograms.natural).precompose binaryHeisenbergEdgeEquiv

noncomputable def encodedBondLeft : Procedure binaryHeisenbergEdgeCodec.encode Nat.bits
    BinaryHeisenbergEdge.left :=
  EncodingPrograms.naturalInput.comp ((Procedure.first _ _).comp encodedBondTuple)

noncomputable def encodedBondRest : Procedure binaryHeisenbergEdgeCodec.encode
    (prodCode BinaryEncoding.natural.encode binaryRationalCodec.encode)
    (fun e => (e.right, e.coefficient)) :=
  (SourcePrograms.pairInput _ _ PrefixPrograms.natural).comp
    ((Procedure.second _ _).comp encodedBondTuple)

noncomputable def encodedBondRight : Procedure binaryHeisenbergEdgeCodec.encode Nat.bits
    BinaryHeisenbergEdge.right :=
  EncodingPrograms.naturalInput.comp ((Procedure.first _ _).comp encodedBondRest)

noncomputable def encodedBondWeight : Procedure binaryHeisenbergEdgeCodec.encode ratCode
    (fun e => e.coefficient.value) :=
  SourcePrograms.rationalValue.comp ((Procedure.second _ _).comp encodedBondRest)

noncomputable def encodedBond : Procedure binaryHeisenbergEdgeCodec.encode bondCode
    (fun e => (e.left, e.right, e.coefficient.value)) :=
  encodedBondLeft.pair (encodedBondRight.pair encodedBondWeight)

noncomputable def sourceBonds : Procedure binaryHeisenbergCodec.encode (listCode bondCode)
    (fun d => d.edges.map (fun e => (e.left, e.right, e.coefficient.value))) :=
  (Procedure.listMap ⟨0, 0, ⟨0, 1⟩⟩ zeroBond encodedBond).comp SourcePrograms.edges

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

def inputCode : Input → List Bool := prodCode unaryCode bondCode

noncomputable def mProgram : Procedure inputCode ratCode (fun x => (x.1 : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp (Procedure.first _ _))
noncomputable def weightProgram : Procedure inputCode ratCode (fun x => x.2.2.2) :=
  ((Procedure.second _ _).comp (Procedure.second _ _)).comp (Procedure.second _ _)
noncomputable def roundedProgram : Procedure inputCode intCode
    (fun x => round ((x.1 : ℚ) * x.2.2.2)) :=
  ChargePrograms.rationalRoundProgram.comp (Procedure.ratMul.comp (mProgram.pair weightProgram))
noncomputable def coefficientProgram : Procedure inputCode ratCode
    (fun x => coefficient x.1 x.2.2.2) :=
  Procedure.ratDiv.comp ((Procedure.intToRat.comp roundedProgram).pair mProgram)

noncomputable def bondProgram : Procedure inputCode bondCode
    (fun x => (x.2.1, x.2.2.1, coefficient x.1 x.2.2.2)) := by
  let bond := Procedure.second unaryCode bondCode
  let left := (Procedure.first Nat.bits (prodCode Nat.bits ratCode)).comp bond
  let right := ((Procedure.first Nat.bits ratCode).comp (Procedure.second Nat.bits _)).comp bond
  exact left.pair (right.pair coefficientProgram)

noncomputable def listProgram : Procedure (prodCode unaryCode (listCode bondCode))
    (listCode bondCode) (fun x => x.2.map (fun e => (e.1, e.2.1, coefficient x.1 e.2.2))) :=
  Procedure.listMapWith (ea := unaryCode) (eb := bondCode) (ec := bondCode)
    (f := fun (M : ℕ) (e : Bond) => (e.1, e.2.1, coefficient M e.2.2))
    zeroBond zeroBond bondProgram

end ContinuumCoulomb.SourceCoefficientRounding

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceZeroFilter
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.edges_length _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.lower_value _root_.OAI.ContinuumCoulomb.QuantumLatticeSerialization.upper_value _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual deletion of zero source bonds after common-denominator rounding. -/

namespace ContinuumCoulomb.SourceZeroFilter
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

theorem filter_code_le (xs : List Bond) :
    (listCode bondCode (xs.filter keep)).length ≤ (listCode bondCode xs).length := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
    by_cases h : keep e = true
    · rw [List.filter_cons_of_pos h]
      simp only [listCode_length_cons]
      omega
    · rw [List.filter_cons_of_neg h]
      simp only [listCode_length_cons]
      omega

noncomputable def isZero : Procedure bondCode Procedure.boolCode (fun e => decide (e.2.2 = 0)) :=
  (Procedure.binaryZero.comp (Procedure.intAbs.comp (Procedure.ratNum.comp
    ((Procedure.second _ _).comp (Procedure.second _ _))))).congrFun (by
      intro e
      simp only [Function.comp_apply, Int.natAbs_eq_zero, Rat.num_eq_zero])

noncomputable def stepProgram : Procedure (prodCode bondCode (listCode bondCode)) (listCode bondCode)
    (fun x => step x.2 x.1) := by
  let test := isZero.comp (Procedure.first bondCode (listCode bondCode))
  let acc := Procedure.second bondCode (listCode bondCode)
  exact (Procedure.conditional test acc (Procedure.listCons bondCode)).congrFun (by
    intro x
    unfold step keep
    by_cases h : x.1.2.2 = 0 <;> simp [h])

noncomputable def foldProgram : Procedure (prodCode (listCode bondCode) (listCode bondCode))
    (listCode bondCode) (fun x => x.1.foldl step x.2) :=
  Procedure.foldList zeroBond stepProgram Polynomial.X (by
    intro xs acc i
    rw [fold_step]
    have h := listCode_length_append bondCode ((xs.take i).filter keep).reverse acc
    rw [listCode_length_rev] at h
    have ht := (filter_code_le (xs.take i)).trans (listCode_length_take_le bondCode i xs)
    simp only [Polynomial.eval_X]
    omega)

noncomputable def filterProgram : Procedure (listCode bondCode) (listCode bondCode)
    (fun xs => xs.filter keep) :=
  ((Procedure.listReverse bondCode zeroBond).comp (foldProgram.comp
    ((Procedure.identity (listCode bondCode)).pair
      (Procedure.constant (listCode bondCode) (listCode bondCode) [])))).congrFun
      (by intro xs; simp only [Function.comp_apply, id_eq, fold_step, List.append_nil, List.reverse_reverse])

end ContinuumCoulomb.SourceZeroFilter

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

noncomputable opaque xsProgram : Procedure inputCode (listCode bondCode) Prod.snd :=
  Procedure.second _ _
noncomputable opaque environment : Procedure inputCode envCode Prod.fst := Procedure.first _ _
noncomputable opaque lengthProgram : Procedure inputCode unaryCode (fun x => x.2.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode zeroBond).comp xsProgram
noncomputable opaque wProgram : Procedure inputCode unaryCode (fun x => x.1.2.1) :=
  ((Procedure.first unaryCode _).comp (Procedure.second unaryCode _)).comp environment
noncomputable opaque gProgram : Procedure inputCode unaryCode (fun x => x.1.2.2.1) :=
  (((Procedure.first unaryCode unaryCode).comp (Procedure.second unaryCode _)).comp
    (Procedure.second unaryCode _)).comp environment
noncomputable opaque nProgram : Procedure inputCode unaryCode (fun x => x.1.2.2.2) :=
  (((Procedure.second unaryCode unaryCode).comp (Procedure.second unaryCode _)).comp
    (Procedure.second unaryCode _)).comp environment

noncomputable opaque denominatorProgram : Procedure inputCode unaryCode
    (fun x => SourceNormalizedSpectrum.denominator x.2.length x.1.2.2.1) := by
  let rPlus : Procedure inputCode unaryCode (fun x => x.2.length + 1) :=
    Procedure.unarySuccessor.comp lengthProgram
  let base : Procedure inputCode unaryCode (fun x => 1024 * (x.2.length + 1)) :=
    mul.comp ((Procedure.constant inputCode unaryCode 1024).pair rPlus)
  exact (mul.comp (base.pair gProgram)).congrFun (by intro x; rfl)

noncomputable opaque roundList : Procedure (prodCode unaryCode (listCode bondCode))
    (listCode bondCode) (fun x => x.2.map (fun e =>
      (e.1, e.2.1, SourceCoefficientRounding.coefficient x.1 e.2.2))) :=
  SourceCoefficientRounding.listProgram
noncomputable opaque roundedProgram : Procedure inputCode (listCode bondCode) rounded := by
  let p : Procedure inputCode (prodCode unaryCode (listCode bondCode))
      (fun x => (SourceNormalizedSpectrum.denominator x.2.length x.1.2.2.1, x.2)) :=
    denominatorProgram.pair xsProgram
  exact (roundList.comp p).congrFun (by intro x; rfl)
noncomputable opaque retainedProgram : Procedure inputCode (listCode bondCode) retained :=
  SourceZeroFilter.filterProgram.comp roundedProgram
noncomputable opaque retainedLength : Procedure inputCode unaryCode
    (fun x => (retained x).length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode zeroBond).comp retainedProgram
noncomputable opaque boundProgram : Procedure inputCode unaryCode
    (fun x => SourceNormalizedSpectrum.denominator x.2.length x.1.2.2.1 + x.1.2.1 + 1) :=
  Procedure.unarySuccessor.comp (add.comp (denominatorProgram.pair wProgram))

noncomputable opaque normalizedEnv : Procedure inputCode envCode (fun x => (normalized x).1) :=
  retainedLength.pair (boundProgram.pair (gProgram.pair nProgram))
noncomputable opaque normalizedProgram : Procedure inputCode inputCode normalized :=
  normalizedEnv.pair retainedProgram

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

noncomputable def boundProgram : (k : ℕ) → Procedure binaryHeisenbergCodec.encode unaryCode
    (fun d => size d ^ k)
  | 0 => Procedure.constant _ unaryCode 1
  | k + 1 => (SourceNormalizationProgram.mul.comp ((boundProgram k).pair sizeProgram)).congrFun
      (by intro d; exact (pow_succ (size d) k).symm)

noncomputable opaque edgeCount : Procedure binaryHeisenbergCodec.encode unaryCode
    (fun d => d.edges.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength
    binaryHeisenbergEdgeCodec.encode ⟨0, 0, ⟨0, 1⟩⟩).comp SourcePrograms.edges

noncomputable opaque environment (k : ℕ) : Procedure binaryHeisenbergCodec.encode envCode
    (fun d => (input k d).1) :=
  edgeCount.pair ((boundProgram k).pair ((boundProgram k).pair vertexCount))
noncomputable opaque inputProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode inputCode
    (input k) := (environment k).pair MediatorListProgram.sourceBonds

noncomputable def normalizedProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode inputCode
    (fun d => SourceNormalizationProgram.normalized (input k d)) :=
  SourceNormalizationProgram.normalizedProgram.comp (inputProgram k)

end ContinuumCoulomb.SourceMetadataProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_MediatorThreeStageProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite-stack program for all three simultaneous mediator
stages. It retains the first central bonds, subdivides the first spokes,
then subdivides all resulting six-bond paths. -/

namespace ContinuumCoulomb.MediatorThreeStageProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque environment : Procedure inputCode envCode Prod.fst := Procedure.first _ _

noncomputable opaque secondInput : Procedure inputCode inputCode
    (fun x => (MediatorUnaryProgram.secondEnv x.1, MediatorListProgram.spokes x)) :=
  (MediatorUnaryProgram.secondProgram.comp environment).pair spokesProgram

noncomputable opaque secondPaths : Procedure inputCode (listCode bondCode)
    (fun x => central (MediatorUnaryProgram.secondEnv x.1, spokes x) ++
      spokes (MediatorUnaryProgram.secondEnv x.1, spokes x)) :=
  stageProgram.comp secondInput

noncomputable opaque thirdInput : Procedure inputCode inputCode
    (fun x => (MediatorUnaryProgram.thirdEnv x.1,
      central (MediatorUnaryProgram.secondEnv x.1, spokes x) ++
        spokes (MediatorUnaryProgram.secondEnv x.1, spokes x))) :=
  (MediatorUnaryProgram.thirdProgram.comp environment).pair secondPaths

def finalBonds (x : Input) : List Bond :=
  central x ++
    central (MediatorUnaryProgram.thirdEnv x.1,
      central (MediatorUnaryProgram.secondEnv x.1, spokes x) ++
        spokes (MediatorUnaryProgram.secondEnv x.1, spokes x)) ++
    spokes (MediatorUnaryProgram.thirdEnv x.1,
      central (MediatorUnaryProgram.secondEnv x.1, spokes x) ++
        spokes (MediatorUnaryProgram.secondEnv x.1, spokes x))

noncomputable opaque bondsProgram : Procedure inputCode (listCode bondCode) finalBonds :=
  ((Procedure.listAppend bondCode zeroBond).comp
    (centralProgram.pair (stageProgram.comp thirdInput))).congrFun
      (by intro x; exact (List.append_assoc _ _ _).symm)

noncomputable opaque verticesProgram : Procedure inputCode unaryCode
    (fun x => x.1.2.2.2 + 18 * x.1.1) :=
  MediatorUnaryProgram.finalN.comp environment

end ContinuumCoulomb.MediatorThreeStageProgram

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

noncomputable opaque absoluteWeight : Procedure bondCode ratCode (fun e => |e.2.2|) :=
  MediatorProgram.absoluteProgram.comp ((Procedure.second _ _).comp (Procedure.second _ _))

noncomputable opaque totalWeight : Procedure inputCode ratCode
    (fun x => (x.2.map (fun e => |e.2.2|)).sum) :=
  RationalSumProgram.sumProgram.comp
    ((Procedure.listMap zeroBond 0 absoluteWeight).comp (Procedure.second _ _))

noncomputable opaque parameters : Procedure inputCode MediatorProgram.rawCode
    (fun x => (x.1.1, x.1.2.1, x.1.2.2.1, 0)) := by
  let e := Procedure.first envCode (listCode bondCode)
  let r := MediatorUnaryProgram.rProgram.comp e
  let w := MediatorUnaryProgram.wProgram.comp e
  let g := MediatorUnaryProgram.gProgram.comp e
  exact r.pair (w.pair (g.pair (Procedure.constant inputCode ratCode 0)))

noncomputable opaque rRational : Procedure inputCode ratCode (fun x => (x.1.1 : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp
    (MediatorUnaryProgram.rProgram.comp (Procedure.first _ _)))

noncomputable opaque penalty : Procedure inputCode ratCode
    (fun x => (MediatorParameters.delta x.1.1 x.1.2.1 x.1.2.2.1 : ℚ)) :=
  (MediatorProgram.deltaRationalProgram.comp parameters).congrFun (by intro x; rfl)

noncomputable opaque stageOffsetProgram : Procedure inputCode ratCode stageOffset := by
  let three := Procedure.constant inputCode ratCode 3
  let head := Procedure.ratMul.comp ((Procedure.ratMul.comp (three.pair rRational)).pair penalty)
  let tail := Procedure.ratMul.comp (three.pair totalWeight)
  exact Procedure.ratAdd.comp (head.pair tail)

def offset (x : Input) : ℚ :=
  stageOffset x +
    stageOffset (MediatorUnaryProgram.secondEnv x.1, spokes x) +
    stageOffset (MediatorUnaryProgram.thirdEnv x.1,
      central (MediatorUnaryProgram.secondEnv x.1, spokes x) ++
        spokes (MediatorUnaryProgram.secondEnv x.1, spokes x))

noncomputable opaque offsetProgram : Procedure inputCode ratCode offset := by
  let second := offsetCompBeta stageOffsetProgram MediatorThreeStageProgram.secondInput
  let third := offsetCompBeta stageOffsetProgram MediatorThreeStageProgram.thirdInput
  let p := offsetCompBeta Procedure.ratAdd
    ((offsetCompBeta Procedure.ratAdd (stageOffsetProgram.pair second)).pair third)
  exact p

end ContinuumCoulomb.MediatorOffsetProgram

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

def offset (k : ℕ) (d : BinaryHeisenberg) : ℚ := MediatorOffsetProgram.offset (normalized k d)

def output (k : ℕ) (d : BinaryHeisenberg) : Registers where
  coordinate := d.coordinate
  vertices := (normalized k d).1.2.2.2 + 18 * (normalized k d).1.1
  bound := MediatorParameters.finalWeight (normalized k d).1.1
    (normalized k d).1.2.1 (normalized k d).1.2.2.1
  gapScale := SourceMetadataProgram.size d ^ k
  bonds := MediatorThreeStageProgram.finalBonds (normalized k d)
  offset := offset k d
  lower := d.lower.value - offset k d + error k d
  upper := d.upper.value - offset k d - error k d

noncomputable opaque normalizedProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode inputCode
    (normalized k) := SourceMetadataProgram.normalizedProgram k
noncomputable opaque bondsProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode (listCode bondCode)
    (fun d => (output k d).bonds) :=
  MediatorThreeStageProgram.bondsProgram.comp (normalizedProgram k)

end ContinuumCoulomb.SourcePositiveProgram

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

noncomputable opaque program (y z : UnitCoulomb) (f : BinaryHeisenberg → UnitCoulomb)
    (pf : Procedure binaryHeisenbergCodec.encode unitCoulombCodec.encode f) :
    Procedure binaryHeisenbergCodec.encode unitCoulombCodec.encode (value y z f) := by
  let oneSpin := BisectionProgram.rationalLess.comp
    (SourcePrograms.lower.pair (Procedure.constant binaryHeisenbergCodec.encode ratCode 0))
  let small := Procedure.conditional oneSpin
    (Procedure.constant binaryHeisenbergCodec.encode unitCoulombCodec.encode z)
    (Procedure.constant binaryHeisenbergCodec.encode unitCoulombCodec.encode y)
  let test := Procedure.unaryLe.comp (SourceMetadataProgram.vertexCount.pair
    (Procedure.constant binaryHeisenbergCodec.encode unaryCode 1))
  exact (Procedure.conditional test small pf).congrFun
    (by intro d; simp only [Function.comp_apply,value,decide_eq_true_eq])

def reduction (y z : UnitCoulomb) (hy : y ∈ unitCoulombPromise.yes)
    (hz : z ∈ unitCoulombPromise.no) (k : ℕ)
    (f : BinaryHeisenberg → UnitCoulomb)
    (pf : Procedure binaryHeisenbergCodec.encode unitCoulombCodec.encode f)
    (hyes : ∀ (d : BinaryHeisenberg) (hd : d.Valid), d.PolynomialPromise k →
      2 ≤ d.coordinate.length → realSourceGroundEnergy (d.toSource hd) ≤ d.lower.value →
        f d ∈ unitCoulombPromise.yes)
    (hno : ∀ (d : BinaryHeisenberg) (hd : d.Valid), d.PolynomialPromise k →
      2 ≤ d.coordinate.length → (d.upper.value : ℝ) ≤ realSourceGroundEnergy (d.toSource hd) →
        f d ∈ unitCoulombPromise.no) :
    PolynomialManyOne binaryHeisenbergCodec.encode unitCoulombCodec.encode
      (sourceHeisenbergPromise k) unitCoulombPromise where
  map := value y z f
  polynomialTime := (program y z f pf).toTM2
  maps_yes := by
    rintro d ⟨hd,hp,hdy⟩
    have hdyR : realSourceGroundEnergy (d.toSource hd) ≤ d.lower.value := by
      apply EReal.coe_le_coe_iff.mp
      rw [realSourceGroundEnergy_coe]
      exact hdy
    by_cases hv : d.coordinate.length ≤ 1
    · have he := source_one_vertex_energy (d.toSource hd) hv
      have hl : ¬d.lower.value < 0 := not_lt.mpr
        (by exact_mod_cast (by linarith [he] : (0:ℝ) ≤ d.lower.value))
      simpa only [value,hv,hl,ite_true, if_true,ite_false, if_false] using hy
    · simpa only [value,hv,ite_false, if_false] using hyes d hd hp (by omega) hdyR
  maps_no := by
    rintro d ⟨hd,hp,hdn⟩
    have hdnR : (d.upper.value : ℝ) ≤ realSourceGroundEnergy (d.toSource hd) := by
      apply EReal.coe_le_coe_iff.mp
      rw [realSourceGroundEnergy_coe]
      exact hdn
    by_cases hv : d.coordinate.length ≤ 1
    · have he := source_one_vertex_energy (d.toSource hd) hv
      have hu : d.upper.value ≤ 0 := by
        exact_mod_cast (by linarith [he] : (d.upper.value:ℝ) ≤ 0)
      have hl : d.lower.value < 0 := lt_of_lt_of_le hd.gap hu
      simpa only [value,hv,hl,ite_true, if_true] using hz
    · simpa only [value,hv,ite_false, if_false] using hno d hd hp (by omega) hdnR

end ContinuumCoulomb.FiniteSourceBranch

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

theorem planarResolventKernel_integral : (∫ r, planarResolventKernel r) = 1 := by
  unfold planarResolventKernel
  rw [← integral_integral_swap (f := fun t r => planarResolventIntegrand (t, r))
    planarResolventIntegrand_integrable]
  calc
    _ = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [planarResolventIntegrand, integral_const_mul, planarHeatKernel_integral ht, mul_one]
    _ = 1 := integral_exp_neg_Ioi_zero

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeDerivatives
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual first and second directional derivatives of the resolvent mode.
Differentiation is transferred to the compact forcing, which also gives
finite L¹ and L² derivatives without differentiating the singular kernel. -/

noncomputable section
open MeasureTheory
open scoped Convolution
namespace ContinuumCoulomb

theorem planarResolventKernel_nonnegative (r : PlanarPosition) :
    0 ≤ planarResolventKernel r := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (Real.exp_pos _).le (planarHeatKernel_positive ht r).le

theorem planarResolventOf_integrable {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) : Integrable (planarResolventOf g) :=
  planarResolventKernel_integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (hg.integrable_of_hasCompactSupport hc)

theorem planarResolventOf_continuous {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) : Continuous (planarResolventOf g) :=
  hc.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    planarResolventKernel_integrable.locallyIntegrable hg

theorem planarResolventOf_bound {g : PlanarPosition → ℝ} {B : ℝ}
    (hB : ∀ x, ‖g x‖ ≤ B) (r : PlanarPosition) : ‖planarResolventOf g r‖ ≤ B := by
  have h := norm_integral_le_of_norm_le (planarResolventKernel_integrable.mul_const B)
    (Filter.Eventually.of_forall (fun b => show
      ‖planarResolventKernel b * g (r - b)‖ ≤ planarResolventKernel b * B by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (planarResolventKernel_nonnegative b)]
      exact mul_le_mul_of_nonneg_left (hB _) (planarResolventKernel_nonnegative b)))
  simpa only [integral_mul_const, planarResolventKernel_integral, one_mul,
    planarResolventOf] using h

theorem planarResolventOf_square_integrable {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) :
    Integrable (fun r => planarResolventOf g r ^ 2) := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hc
  have hi := (planarResolventOf_integrable hg hc).norm.const_mul B
  apply hi.mono' ((planarResolventOf_continuous hg hc).pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun r => by
    change ‖planarResolventOf g r ^ 2‖ ≤ B * ‖planarResolventOf g r‖
    have hb := planarResolventOf_bound hB r
    rw [norm_pow]
    exact (pow_two (‖planarResolventOf g r‖)).trans_le
      (mul_le_mul_of_nonneg_right hb (norm_nonneg _)))

theorem planarResolventOf_partial {g : PlanarPosition → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (e r : PlanarPosition) :
    planarPartial (planarResolventOf g) e r = planarResolventOf (planarPartial g e) r := by
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    planarResolventKernel_integrable.locallyIntegrable hg r
  have hi := (hc.fderiv ℝ).convolutionExists_right
    ((ContinuousLinearMap.mul ℝ ℝ).precompR PlanarPosition)
    planarResolventKernel_integrable.locallyIntegrable
    (hg.continuous_fderiv (by norm_num)) r
  change fderiv ℝ (planarResolventOf g) r e = _
  rw [show fderiv ℝ (planarResolventOf g) r =
    (planarResolventKernel ⋆[((ContinuousLinearMap.mul ℝ ℝ).precompR PlanarPosition), volume]
      fderiv ℝ g) r from hd.fderiv]
  change (∫ b, (ContinuousLinearMap.mul ℝ ℝ).precompR PlanarPosition
    (planarResolventKernel b) (fderiv ℝ g (r - b))) e = _
  rw [ContinuousLinearMap.integral_apply hi e]
  rfl

theorem planarResolventMode_partial (e r : PlanarPosition) :
    planarPartial planarResolventMode e r = planarResolventOf (planarPartial planarForcing e) r :=
  planarResolventOf_partial (planarForcing_C7.of_le (by norm_num))
    planarForcing_hasCompactSupport e r

theorem planarResolventMode_partial_square_integrable (e : PlanarPosition) :
    Integrable (fun r => planarPartial planarResolventMode e r ^ 2) := by
  simp_rw [planarResolventMode_partial]
  exact planarResolventOf_square_integrable
    (planarPartial_continuous (planarForcing_C7.of_le (by norm_num)) e)
    (planarForcing_hasCompactSupport.fderiv_apply ℝ e)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarSobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closure of the actual manufactured-well inequality on the planar
Sobolev graph. The bounded potential acts on actual L² classes, and the
form is continuous in the function-and-gradient norm. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

namespace PlanarSobolev

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasurableSpacePlanarPosition
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instBorelSpacePlanarPosition
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasureSpacePlanarPosition
theorem well_bounded : ∃ B : ℝ, ∀ x, ‖manufacturedPlanarWell x‖ ≤ B :=
  manufacturedPlanarWell_C7.continuous.bounded_above_of_compact_support
    manufacturedPlanarWell_hasCompactSupport

def wellBound : ℝ := Classical.choose well_bounded

theorem wellBound_spec (x : PlanarPosition) :
    ‖manufacturedPlanarWell x‖ ≤ wellBound := Classical.choose_spec well_bounded x

theorem well_mul_memLp (u : Lp ℝ 2 (volume : Measure PlanarPosition)) :
    MemLp (fun x => manufacturedPlanarWell x * u x) 2 := by
  apply (Lp.memLp u).of_le_mul (c := wellBound)
    (manufacturedPlanarWell_C7.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
  exact Filter.Eventually.of_forall (fun x => by
    change ‖manufacturedPlanarWell x * u x‖ ≤ wellBound * ‖u x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (wellBound_spec x) (norm_nonneg _))

def wellMultiply (u : Lp ℝ 2 (volume : Measure PlanarPosition)) :
    Lp ℝ 2 (volume : Measure PlanarPosition) :=
  (well_mul_memLp u).toLp (fun x => manufacturedPlanarWell x * u x)

theorem wellMultiply_ae (u : Lp ℝ 2 (volume : Measure PlanarPosition)) :
    wellMultiply u =ᵐ[volume] fun x => manufacturedPlanarWell x * u x :=
  (well_mul_memLp u).coeFn_toLp

def wellMultiplyLinear : Lp ℝ 2 (volume : Measure PlanarPosition) →ₗ[ℝ]
    Lp ℝ 2 (volume : Measure PlanarPosition) where
  toFun := wellMultiply
  map_add' u v := by
    apply Lp.ext
    filter_upwards [wellMultiply_ae (u + v), wellMultiply_ae u, wellMultiply_ae v,
      Lp.coeFn_add u v, Lp.coeFn_add (wellMultiply u) (wellMultiply v)] with x h h₁ h₂ h₃ h₄
    simp only [h, h₄, h₃, Pi.add_apply, h₁, h₂]
    exact mul_add _ _ _
  map_smul' c u := by
    apply Lp.ext
    change (wellMultiply (c • u) : PlanarPosition → ℝ) =ᵐ[volume]
      (c • wellMultiply u : Lp ℝ 2 volume)
    filter_upwards [wellMultiply_ae (c • u), wellMultiply_ae u,
      Lp.coeFn_smul c u, Lp.coeFn_smul c (wellMultiply u)] with x h h₁ h₂ h₃
    simp only [h, h₃, h₁, h₂, Pi.smul_apply, smul_eq_mul]
    ring

def wellMultiplier : Lp ℝ 2 (volume : Measure PlanarPosition) →L[ℝ]
    Lp ℝ 2 (volume : Measure PlanarPosition) :=
  wellMultiplyLinear.mkContinuous wellBound (fun u =>
    Lp.norm_le_mul_norm_of_ae_le_mul (by
      filter_upwards [wellMultiply_ae u] with x hx
      change ‖wellMultiply u x‖ ≤ wellBound * ‖u x‖
      rw [hx, norm_mul]
      exact mul_le_mul_of_nonneg_right (wellBound_spec x) (norm_nonneg _)))

def form (u : Target) : ℝ :=
  (1 / 2 : ℝ) * ‖u.2‖ ^ 2 + inner ℝ u.1 (wellMultiplier u.1)

open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean in
theorem grad_coordinate (u : PlanarPosition → ℝ) (x : PlanarPosition) (a : Fin 2) :
    grad u x a = planarPartial u (planarAxis a) x := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)
    (x := planarAxis a) (y := fderiv ℝ u x)
  simpa only [grad, planarPartial, planarAxis, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul] using h

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeH1
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasurableSpacePlanarPosition_1
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instBorelSpacePlanarPosition_1
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasureSpacePlanarPosition_1
theorem mode_square_integrable : Integrable (fun x => planarResolventMode x ^ 2) :=
  (planar_integrable_change_borel (borel PlanarPosition) ⟨rfl⟩ _).mpr
    planarResolventMode_square_integrable

theorem mode_memLp : MemLp planarResolventMode 2 :=
  (memLp_two_iff_integrable_sq planarResolventMode_C7.continuous.aestronglyMeasurable).mpr
    mode_square_integrable

theorem grad_norm_sq (f : PlanarPosition → ℝ) (x : PlanarPosition) :
    ‖grad f x‖ ^ 2 = ∑ a : Fin 2, planarPartial f (planarAxis a) x ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_congr rfl (fun a _ => congrArg (fun t : ℝ => t ^ 2) (grad_coordinate f x a))

theorem mode_grad_square_integrable : Integrable (fun x => ‖grad planarResolventMode x‖ ^ 2) := by
  have hi (a : Fin 2) : Integrable (fun x => planarPartial planarResolventMode (planarAxis a) x ^ 2) :=
    (planar_integrable_change_borel (borel PlanarPosition) ⟨rfl⟩ _).mpr
      (planarResolventMode_partial_square_integrable (planarAxis a))
  have h := integrable_finsetSum Finset.univ (fun a _ => hi a)
  exact h.congr (Filter.Eventually.of_forall (fun x => (grad_norm_sq planarResolventMode x).symm))

theorem mode_grad_memLp : MemLp (grad planarResolventMode) 2 :=
  (memLp_two_iff_integrable_sq_norm
    (continuous_grad (planarResolventMode_C7.of_le (by norm_num))).aestronglyMeasurable).mpr
      mode_grad_square_integrable

def cutoffMode (n : ℕ) : Test := ⟨fun x => cutoff n x * planarResolventMode x,
  ⟨((cutoff_smooth n).of_le (by first | simp | exact_mod_cast le_top)).mul (planarResolventMode_C7.of_le (by norm_num)),
    (cutoff_hasCompactSupport n).mul_right⟩⟩

theorem cutoffMode_grad (n : ℕ) (x : PlanarPosition) :
    grad (cutoffMode n).val x = cutoff n x • grad planarResolventMode x +
      planarResolventMode x • grad (cutoff n) x := by
  ext a
  rw [grad_coordinate]
  change planarPartial (fun y => cutoff n y * planarResolventMode y) (planarAxis a) x = _
  rw [planarPartial_mul _ _ ((cutoff_smooth n).of_le (by first | simp | exact_mod_cast le_top))
    (planarResolventMode_C7.of_le (by norm_num))]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, grad_coordinate]

theorem cutoffMode_grad_tendsto (x : PlanarPosition) :
    Tendsto (fun n => grad (cutoffMode n).val x) atTop (𝓝 (grad planarResolventMode x)) := by
  simp_rw [cutoffMode_grad]
  simpa only [one_smul, smul_zero, add_zero] using
    ((cutoff_tendsto x).smul_const (grad planarResolventMode x)).add
      ((tendsto_const_nhds (x := planarResolventMode x)).smul (cutoff_grad_tendsto x))

theorem cutoffMode_value_integral_tendsto :
    Tendsto (fun n => ∫ x, ‖(cutoffMode n).val x - planarResolventMode x‖ ^ 2)
      atTop (𝓝 0) := by
  have h : Tendsto (fun n => ∫ x, ‖(cutoffMode n).val x - planarResolventMode x‖ ^ 2)
      atTop (𝓝 (∫ _ : PlanarPosition, (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence (fun x => planarResolventMode x ^ 2)
    · intro n
      exact (((cutoffMode n).property.1.continuous.sub
        planarResolventMode_C7.continuous).norm.pow 2).aestronglyMeasurable
    · exact mode_square_integrable
    · intro n
      filter_upwards [] with x
      change ‖‖(cutoffMode n).val x - planarResolventMode x‖ ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs, sq_abs]
      change (cutoff n x * planarResolventMode x - planarResolventMode x) ^ 2 ≤ _
      have ha := mul_nonneg (cutoff_nonnegative n x) (planarResolventMode_positive x).le
      have hb := mul_le_of_le_one_left (planarResolventMode_positive x).le (cutoff_le_one n x)
      have hab := mul_nonneg ha (sub_nonneg.mpr hb)
      nlinarith
    · filter_upwards [] with x
      change Tendsto (fun n => ‖cutoff n x * planarResolventMode x - planarResolventMode x‖ ^ 2)
        atTop (𝓝 0)
      have hlim := ((cutoff_tendsto x).mul_const (planarResolventMode x)).sub
        (tendsto_const_nhds (x := planarResolventMode x))
      simpa only [one_mul, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
        hlim.norm.pow 2
  simpa only [integral_zero] using h

theorem cutoffMode_grad_integral_tendsto :
    Tendsto (fun n => ∫ x, ‖grad (cutoffMode n).val x - grad planarResolventMode x‖ ^ 2)
      atTop (𝓝 0) := by
  have hi : Integrable (fun x => 8 * ‖grad planarResolventMode x‖ ^ 2 +
      2 * cutoffGradBound ^ 2 * planarResolventMode x ^ 2) :=
    (mode_grad_square_integrable.const_mul 8).add
      (mode_square_integrable.const_mul (2 * cutoffGradBound ^ 2))
  have h : Tendsto (fun n => ∫ x, ‖grad (cutoffMode n).val x - grad planarResolventMode x‖ ^ 2)
      atTop (𝓝 (∫ _ : PlanarPosition, (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => 8 * ‖grad planarResolventMode x‖ ^ 2 +
        2 * cutoffGradBound ^ 2 * planarResolventMode x ^ 2)
    · intro n
      exact (((continuous_grad (cutoffMode n).property.1).sub
        (continuous_grad (planarResolventMode_C7.of_le (by norm_num)))).norm.pow 2).aestronglyMeasurable
    · exact hi
    · intro n
      filter_upwards [] with x
      change ‖‖grad (cutoffMode n).val x - grad planarResolventMode x‖ ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb : ‖grad (cutoffMode n).val x - grad planarResolventMode x‖ ≤
          2 * ‖grad planarResolventMode x‖ + cutoffGradBound * ‖planarResolventMode x‖ := by
        apply (norm_sub_le _ _).trans
        rw [cutoffMode_grad]
        have ha := norm_add_le (cutoff n x • grad planarResolventMode x)
          (planarResolventMode x • grad (cutoff n) x)
        rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonnegative n x)] at ha
        have h₁ := mul_le_of_le_one_left (norm_nonneg (grad planarResolventMode x))
          (cutoff_le_one n x)
        have h₂ := mul_le_mul_of_nonneg_left (cutoff_grad_bound n x) (norm_nonneg (planarResolventMode x))
        nlinarith
      have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      have hs := sq_nonneg (2 * ‖grad planarResolventMode x‖ - cutoffGradBound * ‖planarResolventMode x‖)
      simp only [Real.norm_eq_abs, abs_of_pos (planarResolventMode_positive x)] at hb2 hs
      nlinarith
    · filter_upwards [] with x
      have hlim := (cutoffMode_grad_tendsto x).sub
        (tendsto_const_nhds (x := grad planarResolventMode x))
      simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using hlim.norm.pow 2
  simpa only [integral_zero] using h

def modeTarget : Target := ⟨mode_memLp.toLp planarResolventMode,
  mode_grad_memLp.toLp (grad planarResolventMode)⟩

theorem cutoffMode_graph_tendsto :
    Tendsto (fun n => graph (μ := volume) (cutoffMode n)) atTop (𝓝 modeTarget) := by
  have hval := toLp_tendsto_of_integral_sub_sq
    (fun n => memLp_of_mem_C1c (μ := volume) (cutoffMode n).property) mode_memLp
      cutoffMode_value_integral_tendsto
  have hgrad := toLp_tendsto_of_integral_sub_sq
    (fun n => memLp_grad_of_mem_C1c (μ := volume) (cutoffMode n).property) mode_grad_memLp
      cutoffMode_grad_integral_tendsto
  exact hval.prodMk_nhds hgrad

theorem modeTarget_mem : modeTarget ∈ Sobolev := by
  apply (isClosed_h1 (μ := volume) (E := PlanarPosition)).mem_of_tendsto cutoffMode_graph_tendsto
  exact Filter.Eventually.of_forall (fun n => subset_closure
    (show graph (μ := volume) (cutoffMode n) ∈
      (LinearMap.range (graph (μ := volume) (E := PlanarPosition)) : Set Target) from
        ⟨cutoffMode n, rfl⟩))

/-- The positive resolvent mode belongs to the closed H¹ graph. -/
def mode : Sobolev := ⟨modeTarget, modeTarget_mem⟩

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarLocalization
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual compact localization on the planar Sobolev graph. Multiplication
by a compactly supported C¹ function is constructed on L² classes and their gradients,
then factored through the proved supported Rellich inclusion. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Topology
namespace ContinuumCoulomb
namespace PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instLocalizationMeasurable
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instLocalizationBorel
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instLocalizationMeasure
theorem testProduct_grad (h u : Test) (x : PlanarPosition) :
    grad (testProduct h u).val x = h.val x • grad u.val x + u.val x • grad h.val x := by
  ext a
  rw [grad_coordinate]
  change planarPartial (fun y => h.val y * u.val y) (planarAxis a) x = _
  rw [planarPartial_mul _ _ h.property.1 u.property.1]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, grad_coordinate]

theorem testTargetMultiplier_graph (h u : Test) :
    testTargetMultiplier h (graph (μ := volume) u) = graph (μ := volume) (testProduct h u) := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [(testScalarField h ℝ).applyLp_ae (toL2 (μ := volume) u),
      (memLp_of_mem_C1c (μ := volume) u.property).coeFn_toLp,
      (memLp_of_mem_C1c (μ := volume) (testProduct h u).property).coeFn_toLp] with x hx hu hv
    change (testScalarField h ℝ).applyLp (toL2 (μ := volume) u) x =
      toL2 (μ := volume) (testProduct h u) x
    change toL2 (μ := volume) u x = u.val x at hu
    change toL2 (μ := volume) (testProduct h u) x = (testProduct h u).val x at hv
    rw [hx, hu, hv]
    rfl
  · apply Lp.ext
    filter_upwards [(testScalarField h PlanarPosition).applyLp_ae (toL2Grad (μ := volume) u),
      (testGradientField h).applyLp_ae (toL2 (μ := volume) u),
      Lp.coeFn_add ((testScalarField h PlanarPosition).applyLp (toL2Grad (μ := volume) u))
        ((testGradientField h).applyLp (toL2 (μ := volume) u)),
      (memLp_of_mem_C1c (μ := volume) u.property).coeFn_toLp,
      (memLp_grad_of_mem_C1c (μ := volume) u.property).coeFn_toLp,
      (memLp_grad_of_mem_C1c (μ := volume) (testProduct h u).property).coeFn_toLp]
      with x hx hx' hadd hu hg hv
    change (((testScalarField h PlanarPosition).applyLp (toL2Grad (μ := volume) u)) +
      (testGradientField h).applyLp (toL2 (μ := volume) u)) x = toL2Grad (μ := volume) (testProduct h u) x
    change toL2 (μ := volume) u x = u.val x at hu
    change toL2Grad (μ := volume) u x = grad u.val x at hg
    change toL2Grad (μ := volume) (testProduct h u) x = grad (testProduct h u).val x at hv
    rw [hadd]
    change (testScalarField h PlanarPosition).applyLp (toL2Grad (μ := volume) u) x +
      (testGradientField h).applyLp (toL2 (μ := volume) u) x = _
    rw [hx, hx', hu, hg, hv, testProduct_grad]
    rfl

theorem testTargetMultiplier_mem (h : Test) (u : Sobolev) : testTargetMultiplier h u.val ∈ Sobolev := by
  have hc : IsClosed {v : Target | testTargetMultiplier h v ∈ Sobolev} :=
    (isClosed_h1 (μ := volume) (E := PlanarPosition)).preimage (testTargetMultiplier h).continuous
  apply closure_minimal (s := (LinearMap.range (graph (μ := volume) (E := PlanarPosition)) : Set Target))
    (t := {v : Target | testTargetMultiplier h v ∈ Sobolev}) ?_ hc u.property
  rintro _ ⟨v, rfl⟩
  change testTargetMultiplier h (graph (μ := volume) v) ∈ Sobolev
  rw [testTargetMultiplier_graph]
  exact subset_closure ⟨testProduct h v, rfl⟩

def testSobolevMultiplier (h : Test) : Sobolev →L[ℝ] Sobolev :=
  ((testTargetMultiplier h).comp Sobolev.subtypeL).codRestrict Sobolev (testTargetMultiplier_mem h)

def testLocalizedL2 (h : Test) : Sobolev →L[ℝ] Lp ℝ 2 (volume : Measure PlanarPosition) :=
  (h1ToL2 (μ := volume) (E := PlanarPosition)).comp (testSobolevMultiplier h)

theorem testLocalizedL2_ae (h : Test) (u : Sobolev) :
    testLocalizedL2 h u =ᵐ[volume] fun x => h.val x * u.val.1 x := by
  exact (testScalarField h ℝ).applyLp_ae u.val.1

theorem testSobolevMultiplier_supported (h : Test) (u : Sobolev) :
    testSobolevMultiplier h u ∈ h1On (tsupport h.val) (isClosed_tsupport h.val).measurableSet := by
  apply mem_extendByZero_range
  filter_upwards [testLocalizedL2_ae h u] with x hx
  intro hxs
  change testLocalizedL2 h u x = 0
  rw [hx, image_eq_zero_of_notMem_tsupport hxs, zero_mul]

def testSupportedMultiplier (h : Test) :
    Sobolev →L[ℝ] h1On (tsupport h.val) (isClosed_tsupport h.val).measurableSet :=
  (testSobolevMultiplier h).codRestrict _ (testSobolevMultiplier_supported h)

def wellTest : Test := ⟨manufacturedPlanarWell,
  ⟨manufacturedPlanarWell_C7.of_le (by norm_num), manufacturedPlanarWell_hasCompactSupport⟩⟩

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarWellBottom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact variational bottom of the manufactured planar well on its
closed Sobolev graph. This is an analytic component of the continuum
construction; it does not assert the hardness reduction. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb
namespace PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasurableSpacePlanarPosition_2
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instBorelSpacePlanarPosition_2
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasureSpacePlanarPosition_2
def normalizedMode : Sobolev := (Real.sqrt (‖mode.val.1‖ ^ 2))⁻¹ • mode

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarSpectralInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The published negative-ground-energy gap consequence used conditionally.

Gerald Teschl, *Mathematical Methods in Quantum Mechanics*, second edition,
AMS Graduate Studies in Mathematics 157 (2014), Theorems 10.2, 10.13 and
4.12 (including its quadratic-form-domain version).
Author's text: https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe2.pdf

For a bounded compactly supported real potential in dimension two, Theorem
10.2 gives the self-adjoint Schrödinger operator, its smooth compact core and
essential spectrum `[0,∞)`. Theorem 10.13 makes an attained ground energy
simple. At a negative ground energy the next max-min value is strictly larger;
Theorem 4.12 states the corresponding inequality on the form domain. Below
we assume only that useful form consequence, then apply it to the actual
manufactured well and its attained bottom. The spectral consequence is
a premise of this conditional interface. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb
namespace PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance instSpectralInputMeasurable_rf0f7f6_1 : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instSpectralInputBorel_rf0f7f6_1 : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instSpectralInputMeasure_rf0f7f6_1 : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace
/-- The single well-specific consequence actually used by the construction. -/
def ManufacturedPlanarGroundGap : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ u : Sobolev,
    inner ℝ u.val.1 normalizedMode.val.1 = 0 →
    ((-1/2:ℝ)+γ)*‖u.val.1‖^2 ≤ form u.val

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarProjectionGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The isolated-well orthogonal gap implies the actual rank-one projection
bound on every vector in the closed Sobolev graph. The ground cross term
vanishes by the proved variational minimum, without a further spectral input. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasurableSpacePlanarPosition_3
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instBorelSpacePlanarPosition_3
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instMeasureSpacePlanarPosition_3
def shiftedForm (u : Target) : ℝ := form u + (1/2 : ℝ) * ‖u.1‖ ^ 2

def shiftedCross (u g : Target) : ℝ :=
  inner ℝ u.2 g.2 + inner ℝ u.1 (wellMultiplier g.1) +
    inner ℝ g.1 (wellMultiplier u.1) + inner ℝ u.1 g.1

end ContinuumCoulomb.PlanarSobolev

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarSobolevDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ground-state duality on the full closed planar Sobolev graph. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instPlanarSobolevDualityMeasurable
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instPlanarSobolevDualityBorel
attribute [local instance] OAI.ContinuumCoulomb.PlanarSobolev.instPlanarSobolevDualityMeasure
def groundDualWeight (ψ : Test) (a : Fin 2) (x : PlanarPosition) : ℝ :=
  planarPartial ψ.val (planarAxis a) x/planarResolventMode x

theorem groundDualWeight_continuous (ψ : Test) (a : Fin 2) :
    Continuous (groundDualWeight ψ a) :=
  (planarPartial_continuous ψ.property.1 _).div planarResolventMode_C7.continuous
    (fun x => (planarResolventMode_positive x).ne')

theorem groundDualWeight_compact (ψ : Test) (a : Fin 2) :
    HasCompactSupport (groundDualWeight ψ a) := by
  change HasCompactSupport (fun x => planarPartial ψ.val (planarAxis a) x *
    (planarResolventMode x)⁻¹)
  exact (ψ.property.2.fderiv_apply ℝ _).mul_right

theorem groundDualWeight_memLp (ψ : Test) (a : Fin 2) : MemLp (groundDualWeight ψ a) 2 :=
  (groundDualWeight_continuous ψ a).memLp_of_hasCompactSupport (groundDualWeight_compact ψ a)

def groundDualLp (ψ : Test) (a : Fin 2) : Lp ℝ 2 (volume : Measure PlanarPosition) :=
  (groundDualWeight_memLp ψ a).toLp (groundDualWeight ψ a)

end ContinuumCoulomb.PlanarSobolev

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

def value (rho : ℕ) (a : ℚ) (C : ℕ) (ε c : ℚ) (k A B : ℕ)
    (x : AutomaticCalibration.Input) : ℚ :=
  AutomaticCalibration.value rho ε c k A B (input a C x)
def normalizedValue (rho : ℕ) (a : ℚ) (C : ℕ) (ε c : ℚ) (k A B : ℕ)
    (x : AutomaticCalibration.Input) : ℚ :=
  value rho a C ε c k A B x / AutomaticCalibration.spacing c k x.1

end ContinuumCoulomb.PrefactorCalibration

end

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

def fieldDivergence (v : Position → Position) (x : Position) : ℝ :=
  ∑ a : Fin 3, NeutralAtom.dirPartial (fun y => v y a) (NeutralAtom.axis a) x

/-- Smooth dependence, Liouville's equation and a uniform finite-order variational estimate. -/
structure PublishedC4FlowInput : Prop where
  regularity : ∀ (U : Set (ℝ × Position)), IsOpen U →
    Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set Position) ⊆ U →
    ∀ v : ℝ → Position → Position,
    ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U →
    ∀ G : Position → ℝ → Position, IsUnitTimeFlow v G →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiff ℝ 4 (fun x => G x t)) ∧
      (∀ x t, t ∈ Set.Icc (0 : ℝ) 1 →
        HasDerivWithinAt (fun s => flowJacobian G s x)
          (fieldDivergence (v t) (G x t) * flowJacobian G t x)
          (Set.Icc (0 : ℝ) 1) t)
  uniform : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 < C ∧
    ∀ (U : Set (ℝ × Position)), IsOpen U →
    Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set Position) ⊆ U →
    ∀ v : ℝ → Position → Position,
    ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U →
    (∀ r ≤ 4, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ r (fun p : ℝ × Position => v p.1 p.2) (t,x)‖ ≤ B) →
    ∀ G : Position → ℝ → Position, IsUnitTimeFlow v G →
    ∀ r : ℕ, 1 ≤ r → r ≤ 4 → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ r (fun y => G y t) x‖ ≤ C

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PrefactorCalibrationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed rational prefactor needs only two extra arithmetic operations
before the existing certified calibration program. -/

namespace ContinuumCoulomb.PrefactorCalibration
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque weightProgram (a : ℚ) : Procedure ratCode ratCode (adjustedWeight a) :=
  Procedure.ratDiv.comp ((Procedure.identity ratCode).pair
    (Procedure.constant ratCode ratCode (a^2)))

end ContinuumCoulomb.PrefactorCalibration

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

noncomputable opaque coordinateProgram : Procedure SourcePrograms.coordinateCodec.encode
    ContactCanonicalEdgeProgram.latticeCode id := by
  let parsed := SourcePrograms.pairInput BinaryEncoding.integer BinaryEncoding.integer
    PrefixPrograms.integer
  exact ((EncodingPrograms.integerInput.comp ((Procedure.first _ _).comp parsed)).pair
    (EncodingPrograms.integerInput.comp ((Procedure.second _ _).comp parsed))).result
      (by intro x; rfl)

noncomputable opaque coordinatesProgram : Procedure binaryHeisenbergCodec.encode
    (listCode ContactCanonicalEdgeProgram.latticeCode) BinaryHeisenberg.coordinate :=
  ((Procedure.listMap (0,0) (0,0) coordinateProgram).comp SourcePrograms.coordinates).result
    (by intro d; simp only [Function.comp_apply,List.map_id])

noncomputable opaque signedBondsProgram (s : ℕ) : Procedure binaryHeisenbergCodec.encode
    (listCode MediatorListProgram.bondCode) (fun d => (SourcePositiveProgram.normalized s d).2) :=
  (Procedure.second _ _).comp (SourcePositiveProgram.normalizedProgram s)

noncomputable opaque coefficientProgram : Procedure MediatorListProgram.bondCode ratCode
    (fun e => e.2.2) := (Procedure.second _ _).comp (Procedure.second _ _)

noncomputable opaque coefficientsProgram (s : ℕ) : Procedure binaryHeisenbergCodec.encode
    (listCode ratCode) (fun d => (SourcePositiveProgram.output s d).bonds.map (fun e => e.2.2)) :=
  (Procedure.listMap MediatorListProgram.zeroBond 0 coefficientProgram).comp
    (SourcePositiveProgram.bondsProgram s)

end ContinuumCoulomb.SourceContactProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceContactCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The raw-source program has exactly the normalized lattice geometry and
the full three-stage positive weights, including their original order. -/

noncomputable section
namespace ContinuumCoulomb.SourceContactProgram
open ContactMediator

def weights (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    GlobalEdge (SourceMetadataProgram.geometricSource s d hd) → ℚ :=
  (MediatorIteration.finalGraph (SourceMetadataProgram.geometricSource s d hd).bonds
    (SourcePositiveProgram.sourceBound s d) (SourceMetadataProgram.size d ^ s)).weight

end ContinuumCoulomb.SourceContactProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_PrefactorSourceContactProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Raw-source contact coordinates with precisely the amplification forced
by the unit-charge mesh. The calibration base is the thirtieth power of
the encoded source size, so its amplification is a cube. -/

namespace ContinuumCoulomb.PrefactorSourceContactProgram
open ExactQuantumFactoring.BitStackProgram

def input (a : ℚ) (C s p h : ℕ) (d : BinaryHeisenberg) : CalibratedContactProgram.Input :=
  (SourceContactProgram.size d ^ h,
    ((CalibrationMesh.base (SourceContactProgram.size d),
      PrefactorCalibration.precision C (SourceContactProgram.size d ^ p)),
      (d.coordinate,((SourcePositiveProgram.normalized s d).2,
        ((SourcePositiveProgram.output s d).bonds.map (fun e => e.2.2)).map
          (PrefactorCalibration.adjustedWeight a)))))

noncomputable def value (rho : ℕ) (a : ℚ) (C : ℕ) (ε c : ℚ)
    (s p h k A B : ℕ) (d : BinaryHeisenberg) : List (ℚ×ℚ) :=
  CalibratedContactProgram.value rho ε c k A B (input a C s p h d)

noncomputable opaque coefficientsProgram (a : ℚ) (s : ℕ) :
    Procedure binaryHeisenbergCodec.encode (listCode ratCode)
      (fun d => ((SourcePositiveProgram.output s d).bonds.map (fun e => e.2.2)).map
        (PrefactorCalibration.adjustedWeight a)) :=
  (Procedure.listMap 0 0 (PrefactorCalibration.weightProgram a)).comp
    (SourceContactProgram.coefficientsProgram s)

noncomputable opaque inputProgram (a : ℚ) (C s p h : ℕ) :
    Procedure binaryHeisenbergCodec.encode CalibratedContactProgram.inputCode (input a C s p h) :=
  (SourceContactProgram.powerProgram h).pair
    (((SourceContactProgram.powerProgram 30).pair
      ((PrefactorCalibration.precisionProgram C).comp (SourceContactProgram.powerProgram p))).pair
        (SourceContactProgram.coordinatesProgram.pair
          ((SourceContactProgram.signedBondsProgram s).pair (coefficientsProgram a s))))

noncomputable opaque program (rho : ℕ) (a : ℚ) (C : ℕ) (ε c : ℚ)
    (s p h k A B : ℕ) : Procedure binaryHeisenbergCodec.encode
      (listCode ContactRationalGadget.pointCode) (value rho a C ε c s p h k A B) :=
  (CalibratedContactProgram.program rho ε c k A B).comp (inputProgram a C s p h)

end ContinuumCoulomb.PrefactorSourceContactProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PrefactorSourceContactCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prefactor-aware program retains the exact final graph enumeration,
and calibrates its original weights at the physical unit-charge scale. -/

noncomputable section
namespace ContinuumCoulomb.PrefactorSourceContactProgram
open ContactMediator

def weights (a : ℚ) (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    GlobalEdge (SourceMetadataProgram.geometricSource s d hd) → ℚ :=
  fun e => PrefactorCalibration.adjustedWeight a (SourceContactProgram.weights s d hd e)

end ContinuumCoulomb.PrefactorSourceContactProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PrefactorSourceCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform, executable nominal calibration for the actual positive
three-stage graph, with precisely the amplification of the nuclear mesh. -/

noncomputable section
namespace ContinuumCoulomb.PrefactorSourceContactProgram
open ContactMediator

def nominalDistance (rho : ℕ) (a : ℚ) (C : ℕ) (ε c : ℚ)
    (s p k A B : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
    (e : GlobalEdge (SourceMetadataProgram.geometricSource s d hd)) : ℚ :=
  PrefactorCalibration.value rho a C ε c k A B
    (CalibrationMesh.base (SourceContactProgram.size d),
      (SourceContactProgram.size d ^ p,SourceContactProgram.weights s d hd e))

end ContinuumCoulomb.PrefactorSourceContactProgram

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

abbrev QMAUnaryRow (c : QMACircuit) := Fin c.gates.length × QMAUnaryBasis c

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateLocality
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed verifier gates act on at most two actual qubits. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaGateSites_card (work : ℕ) (g : QMAGate) : (qmaGateSites work g).card ≤ 2 := by
  cases g with
  | hadamard i => simp [qmaGateSites]
  | phaseT i => simp [qmaGateSites]
  | controlledNot i j =>
    by_cases h : qmaQubit work i = qmaQubit work j
    · simp [qmaGateSites,h]
    · simp [qmaGateSites,h]

theorem qmaGateMatrix_local (work : ℕ) (g : QMAGate) :
    QMALocalOn (qmaGateSites work g) (qmaGateMatrix work g) := by
  cases g with
  | hadamard i =>
    apply qmaLocalOn_sourceTensor
    intro k hk
    exact ite_eq_right (by simpa only [qmaGateSites,Finset.mem_singleton] using hk)
  | phaseT i =>
    apply qmaLocalOn_sourceTensor
    intro k hk
    exact ite_eq_right (by simpa only [qmaGateSites,Finset.mem_singleton] using hk)
  | controlledNot i j =>
    let S := qmaGateSites work (.controlledNot i j)
    let ci : {k // k ∈ S} := ⟨qmaQubit work i,by simp [S,qmaGateSites]⟩
    let f : QMASupportBasis S → QMASupportBasis S := fun s k =>
      if k.val = qmaQubit work j ∧ s ci = 1 then Equiv.swap (0:Fin 2) 1 (s k) else s k
    apply qmaLocalOn_permutation S (qmaControlledNot work (qmaQubit work i) (qmaQubit work j)) f
    · intro t
      funext k
      rfl
    · intro t
      funext k
      have hk : k.val ≠ qmaQubit work j := by
        have h := k.property
        simp only [S,qmaGateSites,Finset.mem_insert,Finset.mem_singleton,not_or] at h
        exact h.2
      simp [qmaSupportSplit,Equiv.piEquivPiSubtypeProd,qmaControlledNot,hk]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalPropagation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

def qmaPropagationSites (c : QMACircuit) (t : Fin c.gates.length) : Finset (QMACircuitQubit c) :=
  {Sum.inl (qmaClockLeft c.gates.length t),Sum.inl (qmaClockMiddle c.gates.length t),
    Sum.inl (qmaClockRight c.gates.length t)} ∪
    (qmaGateSites c.work (c.gates.getD t.val (.hadamard 0))).map Function.Embedding.inr

theorem qmaPropagationSites_card (c : QMACircuit) (t : Fin c.gates.length) :
    (qmaPropagationSites c t).card ≤ 5 := by
  have h := Finset.card_union_le
    ({Sum.inl (qmaClockLeft c.gates.length t),Sum.inl (qmaClockMiddle c.gates.length t),
      Sum.inl (qmaClockRight c.gates.length t)} : Finset (QMACircuitQubit c))
    ((qmaGateSites c.work (c.gates.getD t.val (.hadamard 0))).map Function.Embedding.inr)
  have hclock : ({Sum.inl (qmaClockLeft c.gates.length t),
      Sum.inl (qmaClockMiddle c.gates.length t),Sum.inl (qmaClockRight c.gates.length t)} :
      Finset (QMACircuitQubit c)).card ≤ 3 := by
    apply le_trans (Finset.card_insert_le _ _)
    have h2 := Finset.card_insert_le (Sum.inl (qmaClockMiddle c.gates.length t))
      ({Sum.inl (qmaClockRight c.gates.length t)} : Finset (QMACircuitQubit c))
    simp only [Finset.card_singleton] at h2
    omega
  have hgate := qmaGateSites_card c.work (c.gates.getD t.val (.hadamard 0))
  simp only [Finset.card_map] at h
  unfold qmaPropagationSites
  omega

theorem qmaGuardProjection_local (c : QMACircuit) (t : Fin c.gates.length) :
    QMALocalOn (qmaPropagationSites c t) (qmaGuardProjection c t) := by
  apply qmaLocalOn_diagonal
  intro s r h
  have hl := h (Sum.inl (qmaClockLeft c.gates.length t)) (by simp [qmaPropagationSites])
  have hm := h (Sum.inl (qmaClockMiddle c.gates.length t)) (by simp [qmaPropagationSites])
  have hr := h (Sum.inl (qmaClockRight c.gates.length t)) (by simp [qmaPropagationSites])
  simp only [QMAClockGuard,Function.comp_apply,hl,hm,hr]
  split_ifs with hp
  · exact (ite_eq_left hp).symm
  · exact (ite_eq_right hp).symm

theorem qmaLocalPropagationDelta_local (c : QMACircuit) (t : Fin c.gates.length) :
    QMALocalOn (qmaPropagationSites c t) (qmaLocalPropagationDelta c t) := by
  have hf := (qmaBitFlipMatrix_local (Sum.inl (qmaClockMiddle c.gates.length t))).mono
    (T := qmaPropagationSites c t)
    (by intro i hi; simp only [Finset.mem_singleton] at hi; subst i; simp [qmaPropagationSites])
  have hg := ((qmaGateMatrix_local c.work (c.gates.getD t.val (.hadamard 0))).joinRight
    (ι := Fin (c.gates.length+2))).mono (T := qmaPropagationSites c t) (Finset.subset_union_right)
  have hn := hg.smul (-1)
  have hs := hf.add hn
  simp only [neg_one_smul,←sub_eq_add_neg] at hs
  exact (qmaGuardProjection_local c t).mul hs

theorem qmaLocalPropagationGram_local (c : QMACircuit) (t : Fin c.gates.length) :
    QMALocalOn (qmaPropagationSites c t)
      ((qmaLocalPropagationDelta c t).conjTranspose*qmaLocalPropagationDelta c t) :=
  (qmaLocalPropagationDelta_local c t).adjoint.mul (qmaLocalPropagationDelta_local c t)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalFamily
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

def qmaCircuitTermSites (c : QMACircuit) : QMACircuitTerm c → Finset (QMACircuitQubit c)
  | .inl i => {Sum.inl i.castSucc,Sum.inl i.succ}
  | .inr (.inl b) => if b = 0 then {Sum.inl 0} else {Sum.inl (Fin.last (c.gates.length+1))}
  | .inr (.inr (.inl i)) => {Sum.inl (qmaInputMarker c),Sum.inr i}
  | .inr (.inr (.inr (.inl _))) => {Sum.inl (qmaOutputMarker c),Sum.inr (Fin.last c.work)}
  | .inr (.inr (.inr (.inr t))) => qmaPropagationSites c t

def qmaCircuitTermMatrix (c : QMACircuit) : QMACircuitTerm c →
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ
  | .inl i => qmaClockFaultTerm c i
  | .inr (.inl b) => if b = 0 then qmaClockLeftTerm c else qmaClockRightTerm c
  | .inr (.inr (.inl i)) => qmaInputTerm c i
  | .inr (.inr (.inr (.inl _))) => qmaOutputTerm c
  | .inr (.inr (.inr (.inr t))) =>
    (8*c.gates.length:ℂ) • ((qmaLocalPropagationDelta c t).conjTranspose*qmaLocalPropagationDelta c t)

theorem qmaCircuitTerm_support_card (c : QMACircuit) (i : QMACircuitTerm c) :
    (qmaCircuitTermSites c i).card ≤ 5 := by
  have hp (a b : QMACircuitQubit c) : ({a,b} : Finset (QMACircuitQubit c)).card ≤ 2 := by
    have h := Finset.card_insert_le a ({b} : Finset (QMACircuitQubit c))
    simpa only [Finset.card_singleton] using h
  rcases i with i | (b | (i | (u | t)))
  · exact le_trans (hp _ _) (by norm_num : (2:ℕ) ≤ 5)
  · fin_cases b <;> simp [qmaCircuitTermSites]
  · exact le_trans (hp _ _) (by norm_num : (2:ℕ) ≤ 5)
  · exact le_trans (hp _ _) (by norm_num : (2:ℕ) ≤ 5)
  · exact qmaPropagationSites_card c t

theorem qmaCircuitTerm_hermitian (c : QMACircuit) (i : QMACircuitTerm c) :
    (qmaCircuitTermMatrix c i).IsHermitian := by
  have hd (f : (QMACircuitQubit c → Fin 2) → ℂ)
      (hf : ∀ s, star (f s) = f s) : (Matrix.diagonal f).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro s
    exact hf s
  rcases i with i | (b | (i | (u | t)))
  · apply hd
    intro s
    dsimp only
    split_ifs <;> simp
  · fin_cases b <;> apply hd <;> intro s <;> dsimp only <;> split_ifs <;> simp
  · apply hd
    intro s
    dsimp only
    split_ifs <;> simp
  · apply hd
    intro s
    dsimp only
    split_ifs <;> simp
  · exact (Matrix.isHermitian_conjTranspose_mul_self _).smul (by simp [isSelfAdjoint_iff])

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFirstUse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete schedule of initialization checks, one at each qubit's first use. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaFirstUse (c : QMACircuit) (i : Fin (c.work+1)) : ℕ :=
  c.gates.findIdx (fun g => decide (i ∈ qmaGateSites c.work g))

theorem qmaFirstUse_le (c : QMACircuit) (i : Fin (c.work+1)) :
    qmaFirstUse c i ≤ c.gates.length := List.findIdx_le_length

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedFamily
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

def qmaDistributedTermSites (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) : QMACircuitTerm c → Finset (QMACircuitQubit c)
  | .inr (.inr (.inl i)) => qmaDistributedInputSites c τ i
  | t => qmaCircuitTermSites c t

theorem qmaDistributedTerm_local (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (t : QMACircuitTerm c) :
    QMALocalOn (qmaDistributedTermSites c τ t) (qmaDistributedTermMatrix c τ t) := by
  rcases t with i | (b | (i | (u | t)))
  · exact qmaClockFaultTerm_local c i
  · fin_cases b
    · exact qmaClockLeftTerm_local c
    · exact qmaClockRightTerm_local c
  · exact qmaDistributedInputTerm_local c τ i
  · exact qmaOutputTerm_local c
  · exact (qmaLocalPropagationGram_local c t).smul _

theorem qmaDistributedTerm_support_card (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (t : QMACircuitTerm c) :
    (qmaDistributedTermSites c τ t).card ≤ 5 := by
  rcases t with i | (b | (i | (u | t)))
  · exact qmaCircuitTerm_support_card c (.inl i)
  · exact qmaCircuitTerm_support_card c (.inr (.inl b))
  · change (qmaDistributedInputSites c τ i).card ≤ 5
    rw [qmaDistributedInputSites_card]
    norm_num
  · exact qmaCircuitTerm_support_card c (.inr (.inr (.inr (.inl u))))
  · exact qmaPropagationSites_card c t

theorem qmaDistributedTerm_hermitian (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (t : QMACircuitTerm c) :
    (qmaDistributedTermMatrix c τ t).IsHermitian := by
  rcases t with i | (b | (i | (u | t)))
  · exact qmaCircuitTerm_hermitian c (.inl i)
  · exact qmaCircuitTerm_hermitian c (.inr (.inl b))
  · apply Matrix.isHermitian_diagonal_iff.mpr
    intro s
    split_ifs <;> simp
  · exact qmaCircuitTerm_hermitian c (.inr (.inr (.inr (.inl u))))
  · exact (Matrix.isHermitian_conjTranspose_mul_self _).smul (by simp [isSelfAdjoint_iff])

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

def qmaGateCut (work : ℕ) (e : Equiv.Perm (Fin (work+1))) (g : QMAGate) : ℕ :=
  (qmaGateSites work g).sup (fun i => (e.symm i).val)+1

def qmaRowStage (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1)))
    (g : QMAGate) : List QMAGate :=
  let ps := qmaRowPairs (l ∘ e) (r ∘ e)
  qmaTransferGates (ps.take (qmaGateCut width e g)) ++
    [qmaMapGate width work r g] ++
      qmaTransferGates (ps.drop (qmaGateCut width e g))

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

def qmaSweepCircuitFrom (rows width : ℕ) :
    (start : ℕ) → (gs : List QMAGate) → start+gs.length ≤ rows → List QMAGate
  | _,[],_ => []
  | start,g::gs,h =>
      qmaRowStage width (qmaGridWork rows width)
        (qmaGridQubit rows width ⟨start,by simp only [List.length_cons] at h; omega⟩)
        (qmaGridQubit rows width ⟨start+1,by simp only [List.length_cons] at h; omega⟩)
        (qmaSweepOrder width (rows-1-start)) g ++
      qmaSweepCircuitFrom rows width (start+1) gs (by simp only [List.length_cons] at h; omega)

abbrev qmaSweepCircuit (c : QMACircuit) : QMACircuit :=
  ⟨qmaGridWork c.gates.length c.work,c.witness,
    qmaSweepCircuitFrom c.gates.length c.work 0 c.gates (by omega)⟩

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

abbrev qmaSparseCircuit (c : QMACircuit) : QMACircuit := qmaSweepCircuit (qmaNearestCircuit c)

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

theorem qmaDistributedRebitOnQubits_local (n : ℕ) (i : Fin n) {S : Finset ι}
    {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ} (hA : QMALocalOn S A) :
    QMALocalOn (qmaDistributedRebitSites n i S) (qmaDistributedRebitOnQubits n i A) := by
  rw [qmaDistributedRebitOnQubits_eq]
  apply QMALocalOn.add
  · exact hA.entryReal.joinRight.mono (Finset.subset_insert _ _)
  · have h := (qmaLocalY_local n i).join hA.entryImag
    have he : (({i} : Finset (Fin n)).map (Function.Embedding.inl : Fin n ↪ Fin n ⊕ ι) ∪
        S.map Function.Embedding.inr) = qmaDistributedRebitSites n i S := by
      simp [qmaDistributedRebitSites]
    rw [he] at h
    exact h.smul _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceEdges
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem qmaReferenceYEdge_local (n : ℕ) (i : Fin n) :
    QMALocalOn {i.castSucc,i.succ} (qmaReferenceYEdge n i) := by
  have ha := (qmaLocalY_local (n+1) i.castSucc).mono (by simp :
    ({i.castSucc} : Finset (Fin (n+1))) ⊆ {i.castSucc,i.succ})
  have hb := (qmaLocalY_local (n+1) i.succ).mono (by simp :
    ({i.succ} : Finset (Fin (n+1))) ⊆ {i.castSucc,i.succ})
  have h1 : QMALocalOn {i.castSucc,i.succ} (1 : Matrix (SourceSpinBasis (n+1)) _ ℂ) :=
    ⟨1,(qmaLocalLift_one _).symm⟩
  simpa only [qmaReferenceYEdge,sub_eq_add_neg,neg_one_smul] using
    (h1.add ((ha.mul hb).smul (-1))).smul (1/2 : ℂ)

theorem qmaReferenceEdgeOnQubits_local (n : ℕ) (i : Fin n) :
    QMALocalOn (qmaReferenceEdgeSites (ι := ι) n i) (qmaReferenceEdgeOnQubits (ι := ι) n i) := by
  have h := (qmaReferenceYEdge_local n i).joinLeft (κ := ι)
  simpa only [qmaReferenceEdgeSites,qmaReferenceEdgeOnQubits,
    Finset.map_insert,Finset.map_singleton,Function.Embedding.inl_apply] using h

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

theorem qmaReferenceTerm_local (n : ℕ)
    (A : Fin (n+1) → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (S : Fin (n+1) → Finset ι) (hA : ∀ i, QMALocalOn (S i) (A i))
    (t : QMAReferenceTerm n) :
    QMALocalOn (qmaReferenceTermSites n S t) (qmaReferenceTermMatrix n A t) := by
  cases t with
  | inl i => exact qmaDistributedRebitOnQubits_local _ _ (hA i)
  | inr i => exact qmaReferenceEdgeOnQubits_local _ _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A real six-local history model with separate references and a linear term count. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

abbrev qmaFirstUseTime (c : QMACircuit) (i : Fin (c.work+1)) : Fin (c.gates.length+1) :=
  ⟨qmaFirstUse c i,Nat.lt_succ_of_le (qmaFirstUse_le c i)⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The time-ordered real six-local model retains both verifier bounds. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaOrderedHistorySites (c : QMACircuit) (hT : 0 < c.gates.length) (i : Fin (qmaHistoryReferenceWork c+1)) :
    Finset (QMACircuitQubit c) :=
  qmaDistributedTermSites c (qmaFirstUseTime c) (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)

def qmaOrderedHistoryModel (c : QMACircuit) (hT : 0 < c.gates.length) : QMARealLocalModel 6 where
  Q := Fin (qmaHistoryReferenceWork c+1) ⊕ QMACircuitQubit c
  Term := QMAReferenceTerm (qmaHistoryReferenceWork c)
  qFinite := inferInstance
  qDecidable := inferInstance
  termFinite := inferInstance
  matrix := qmaReferenceTermMatrix (qmaHistoryReferenceWork c)
    (qmaOrderedReferenceTerms c hT (qmaFirstUseTime c))
  sites := qmaReferenceTermSites (qmaHistoryReferenceWork c) (qmaOrderedHistorySites c hT)
  localOn := qmaReferenceTerm_local _ _ _ (fun _ => qmaDistributedTerm_local c _ _)
  card := qmaReferenceTerm_card _ _ (fun _ => qmaDistributedTerm_support_card c _ _)
  hermitian := qmaReferenceTerm_hermitian _ _ (fun _ => qmaDistributedTerm_hermitian c _ _)
  real := qmaReferenceTerm_real _ _

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
open PrefixPrograms

noncomputable def sumSplitter {α β : Type}
    (c : BinaryEncoding.Codec α) (d : BinaryEncoding.Codec β)
    (pc : Splitter c) (pd : Splitter d) : Splitter (BinaryEncoding.sum c d) := by
  let outCode := prodCode (BinaryEncoding.sum c d).encode id
  let left : Procedure (prefixCode c) outCode
      (fun x : α × List Bool => (Sum.inl x.1,x.2)) :=
    (((Procedure.sumLeft c.encode d.encode).comp
      ((Procedure.first c.encode id).comp pc)).pair
        ((Procedure.second c.encode id).comp pc)).result (by intro x; rfl)
  let right : Procedure (prefixCode d) outCode
      (fun x : β × List Bool => (Sum.inr x.1,x.2)) :=
    (((Procedure.sumRight c.encode d.encode).comp
      ((Procedure.first d.encode id).comp pd)).pair
        ((Procedure.second d.encode id).comp pd)).result (by intro x; rfl)
  exact (((Procedure.casesSum left right).precompose sumView).congrEncoding
    (by rintro ⟨a,s⟩; cases a <;> rfl) (by intro x; rfl)).congrFun (by
      rintro ⟨a,s⟩
      cases a <;> rfl)

noncomputable def gateSplitter : Splitter qmaGateCodec :=
  SourcePrograms.equivSplitter _ qmaGateEquiv
    (sumSplitter _ _ (sumSplitter _ _ natural natural)
      (PrefixPrograms.pair _ _ natural natural))

noncomputable def gateInput : Procedure qmaGateCodec.encode gateCode id := by
  let left := Procedure.casesSum
    ((Procedure.sumLeft Nat.bits Nat.bits).comp EncodingPrograms.naturalInput)
    ((Procedure.sumRight Nat.bits Nat.bits).comp EncodingPrograms.naturalInput)
  let pairInput := SourcePrograms.pairInput BinaryEncoding.natural BinaryEncoding.natural natural
  let right := ((EncodingPrograms.naturalInput.comp (Procedure.first _ _)).pair
    (EncodingPrograms.naturalInput.comp (Procedure.second _ _))).comp pairInput
  let first := (Procedure.sumLeft (sumCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits)).comp left
  let second := (Procedure.sumRight (sumCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits)).comp right
  exact ((Procedure.casesSum first second).precompose qmaGateEquiv).result (by
    intro g
    cases g <;> rfl)

noncomputable def gateListInput :
    Procedure (BinaryEncoding.list qmaGateCodec).encode (listCode gateCode) id :=
  ((Procedure.listMap (.hadamard 0) (.hadamard 0) gateInput).comp
    (PrefixListPrograms.listInput qmaGateCodec gateSplitter (.hadamard 0) gate_length_pos)).congrFun
      (by intro gs; simp only [Function.comp_apply,List.map_id,id_eq])

noncomputable def circuitTuple :
    Procedure qmaCircuitCodec.encode (prodCode BinaryEncoding.natural.encode tailCodec.encode)
      qmaCircuitEquiv :=
  (SourcePrograms.pairInput BinaryEncoding.natural tailCodec natural).precompose qmaCircuitEquiv

noncomputable def workInput : Procedure qmaCircuitCodec.encode Nat.bits QMACircuit.work :=
  EncodingPrograms.naturalInput.comp ((Procedure.first _ _).comp circuitTuple)

noncomputable def restInput :
    Procedure qmaCircuitCodec.encode
      (prodCode BinaryEncoding.natural.encode (BinaryEncoding.list qmaGateCodec).encode)
      (fun c => (c.witness,c.gates)) :=
  (SourcePrograms.pairInput BinaryEncoding.natural (BinaryEncoding.list qmaGateCodec) natural).comp
    ((Procedure.second _ _).comp circuitTuple)

noncomputable def witnessInput : Procedure qmaCircuitCodec.encode Nat.bits QMACircuit.witness :=
  EncodingPrograms.naturalInput.comp ((Procedure.first _ _).comp restInput)

noncomputable def gatesInput : Procedure qmaCircuitCodec.encode (listCode gateCode) QMACircuit.gates :=
  gateListInput.comp ((Procedure.second _ _).comp restInput)

noncomputable def boundedInput :
    Procedure (prodCode unaryCode qmaCircuitCodec.encode) circuitCode cap := by
  let b := Procedure.first unaryCode qmaCircuitCodec.encode
  let c := Procedure.second unaryCode qmaCircuitCodec.encode
  let work := Procedure.clippedUnary.comp (b.pair (workInput.comp c))
  let witness := Procedure.clippedUnary.comp (b.pair (witnessInput.comp c))
  exact (work.pair (witness.pair (gatesInput.comp c))).result (by intro x; rfl)

noncomputable def nonemptyProgram : Procedure circuitCode circuitCode qmaNonemptyCircuit := by
  let extra := Procedure.constant circuitCode (listCode gateCode)
    [QMAGate.hadamard 0,QMAGate.hadamard 0]
  let gates := (Procedure.listAppend gateCode (.hadamard 0)).comp (gatesProgram.pair extra)
  exact (workProgram.pair (witnessProgram.pair gates)).result (by intro c; rfl)

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal constructors and coordinate selectors for the fixed H/T/CNOT
alphabet used by the nearest-neighbor circuit preprocessor. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram

noncomputable def swapListProgram : Procedure Nat.bits (listCode gateCode) swapList := by
  let a := Procedure.identity Nat.bits
  let b := Procedure.successor
  let forward := cnotProgram.comp (a.pair b)
  let backward := cnotProgram.comp (b.pair a)
  let nil := Procedure.constant Nat.bits (listCode gateCode) []
  let one := (Procedure.listCons gateCode).comp (forward.pair nil)
  let two := (Procedure.listCons gateCode).comp (backward.pair one)
  exact (Procedure.listCons gateCode).comp (forward.pair two)

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAxisSampleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial programs for the algebraic four-spin coupling samples. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque valueProgram (a : Fin 2) : Procedure unaryCode ratCode (fun k => value k a) := by
  by_cases ha : a = 0
  · let root := RationalSquareRoot.program.comp
      ((Procedure.identity unaryCode).pair (Procedure.constant unaryCode ratCode 3))
    exact (Procedure.ratMul.comp (root.pair (Procedure.constant unaryCode ratCode (1/384)))).congrFun
      (by intro k; simp only [value,ha,ite_true, if_true,Function.comp_apply,id_eq]; ring)
  · exact (Procedure.constant unaryCode ratCode (3/4)).congrFun (by intro k; simp only [value,ha,ite_false, if_false])

noncomputable opaque radicandProgram (a b : Fin 2) :
    Procedure radialCode ratCode (fun x => radicand x.1 a b x.2) := by
  let precision := Procedure.first unaryCode ratCode
  let coefficient := Procedure.second unaryCode ratCode
  let absolute := MediatorProgram.absoluteProgram.comp coefficient
  let factor := Procedure.ratMul.comp ((Procedure.constant radialCode ratCode (8/3)).pair absolute)
  let left := (valueProgram a).comp precision
  let right := (valueProgram b).comp precision
  exact (Procedure.ratMul.comp ((Procedure.ratMul.comp (factor.pair left)).pair right)).congrFun
    (by intro x; rfl)

noncomputable opaque couplingProgram (a b : Fin 2) : Procedure couplingCode ratCode
    (fun x => coupling x.1 x.2.1 a b x.2.2) := by
  let inner := Procedure.first unaryCode (prodCode unaryCode ratCode)
  let rest := Procedure.second unaryCode (prodCode unaryCode ratCode)
  let outer := (Procedure.first unaryCode ratCode).comp rest
  let coefficient := (Procedure.second unaryCode ratCode).comp rest
  let argument := (radicandProgram a b).comp (inner.pair coefficient)
  exact (RationalSquareRoot.program.comp (outer.pair argument)).congrFun (by intro x; rfl)

noncomputable opaque calibratedProgram (a b : Fin 2) : Procedure radialCode ratCode (calibrated a b) :=
  ((couplingProgram a b).comp calibratedArgumentsProgram).congrFun (by intro x; rfl)

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCountertermProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal rational arithmetic for the internal four-spin counterterms. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque positiveProgram : Procedure ratCode Procedure.boolCode (fun t : ℚ => decide (0 < t)) :=
  BisectionProgram.rationalLess.comp ((Procedure.constant ratCode ratCode 0).pair (Procedure.identity ratCode))

noncomputable opaque polarityProgram : Procedure ratCode ratCode polarity := by
  exact (Procedure.conditional positiveProgram (Procedure.constant ratCode ratCode (-1))
    (Procedure.constant ratCode ratCode 1)).congrFun (by
      intro t
      by_cases ht : 0 < t
      · simp [polarity,ht,not_le_of_gt ht]
      · simp [polarity,ht,le_of_not_gt ht])

noncomputable opaque shiftProgram (a : Fin 2) : Procedure ratCode ratCode
    (fun t => shift a (decide (t ≤ 0))) := by
  by_cases ha : a = 0
  · exact (Procedure.constant ratCode ratCode 400).congrFun (by intro t; simp [shift,ha])
  · exact (Procedure.conditional positiveProgram (Procedure.constant ratCode ratCode (4/3))
      (Procedure.constant ratCode ratCode (8/3))).congrFun (by
        intro t
        by_cases ht : 0 < t
        · simp [shift,ha,ht,not_le_of_gt ht]
        · simp [shift,ha,ht,le_of_not_gt ht])

noncomputable opaque absoluteInputProgram : Procedure radialCode ratCode (fun x => |x.2|) :=
  MediatorProgram.absoluteProgram.comp inputCoefficientProgram

noncomputable opaque factorProgram (a b : Fin 2) : Procedure radialCode ratCode
    (fun x => factor x.1 a b x.2) := by
  let l := (valueProgram a).comp inputPrecisionProgram
  let r := (valueProgram b).comp inputPrecisionProgram
  exact (Procedure.ratMul.comp ((Procedure.ratMul.comp (absoluteInputProgram.pair l)).pair r)).congrFun
    (by intro x; rfl)

noncomputable opaque counterAProgram (a b : Fin 2) : Procedure radialCode ratCode
    (fun x => counterA x.1 a b x.2) := by
  let v := (valueProgram b).comp inputPrecisionProgram
  let s := (shiftProgram b).comp inputCoefficientProgram
  exact (Procedure.ratMul.comp ((Procedure.ratMul.comp (absoluteInputProgram.pair v)).pair s)).congrFun
    (by intro x; rfl)

noncomputable opaque counterBProgram (a b : Fin 2) : Procedure radialCode ratCode
    (fun x => counterB x.1 a b x.2) := by
  let v := (valueProgram a).comp inputPrecisionProgram
  let sign := polarityProgram.comp inputCoefficientProgram
  let initial := Procedure.ratMul.comp (absoluteInputProgram.pair v)
  let signed := Procedure.ratMul.comp (initial.pair sign)
  exact (Procedure.ratMul.comp (signed.pair (Procedure.constant radialCode ratCode (shift a true)))).congrFun
    (by intro x; rfl)

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFieldSample
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certified rational evaluation of each internal physical field coefficient. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram
open Matrix

noncomputable opaque fieldXProgram : Procedure radialCode ratCode (fun x => fieldX x.1 x.2) := by
  let scalar := Procedure.ratMul.comp ((Procedure.constant radialCode ratCode 64).pair inputCoefficientProgram)
  let v := (valueProgram 0).comp inputPrecisionProgram
  exact (Procedure.ratMul.comp (scalar.pair v)).congrFun (by intro x; rfl)

noncomputable opaque fieldValueProgram (a : Fin 2) (e : Fin 3) : Procedure radialCode ratCode
    (fun x => fieldValue x.1 a x.2 e) := by
  by_cases ha : a = 0
  · by_cases he0 : e = 0
    · subst e
      exact fieldXProgram.congrFun (by intro x; simp [fieldValue,ha])
    · by_cases he1 : e = 1
      · subst e
        exact (Procedure.ratNeg.comp fieldXProgram).congrFun (by intro x; simp [fieldValue,ha])
      · have he2 : e = 2 := by omega
        subst e
        exact (Procedure.constant radialCode ratCode 0).congrFun (by intro x; simp [fieldValue,ha])
  · by_cases he2 : e = 2
    · subst e
      exact (Procedure.ratMul.comp (inputCoefficientProgram.pair
        (Procedure.constant radialCode ratCode (-1/2)))).congrFun (by
          intro x
          simp [fieldValue,ha,Function.comp_apply]
          ring)
    · by_cases he0 : e = 0
      · subst e
        exact (Procedure.constant radialCode ratCode 0).congrFun (by intro x; simp [fieldValue,ha])
      · have he1 : e = 1 := by omega
        subst e
        exact (Procedure.constant radialCode ratCode 0).congrFun (by intro x; simp [fieldValue,ha])

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOffsetProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial programs for the counterterm field coefficients and scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque shiftValueProgram (a : Fin 2) : Procedure ratCode ratCode (shiftValue a) := by
  by_cases ha : a = 0
  · exact (Procedure.constant ratCode ratCode 0).congrFun (by intro t; simp [shiftValue,ha])
  · exact (Procedure.ratMul.comp ((Procedure.identity ratCode).pair
      (Procedure.constant ratCode ratCode (1/2)))).congrFun (by
        intro t
        simp only [shiftValue,ha,ite_false, if_false,Function.comp_apply,id_eq]
        ring)

noncomputable opaque counterFieldAProgram (a b : Fin 2) (e : Fin 3) :
    Procedure radialCode ratCode (fun x => fieldValue x.1 a (counterA x.1 a b x.2) e) :=
  ((fieldValueProgram a e).comp (inputPrecisionProgram.pair (counterAProgram a b))).congrFun
    (by intro x; rfl)

noncomputable opaque counterFieldBProgram (a b : Fin 2) (e : Fin 3) :
    Procedure radialCode ratCode (fun x => fieldValue x.1 b (counterB x.1 a b x.2) e) :=
  ((fieldValueProgram b e).comp (inputPrecisionProgram.pair (counterBProgram a b))).congrFun
    (by intro x; rfl)

noncomputable opaque offsetProgram (a b : Fin 2) : Procedure radialCode ratCode
    (fun x => offset x.1 a b x.2) := by
  let left := (shiftValueProgram a).comp (counterAProgram a b)
  let right := (shiftValueProgram b).comp (counterBProgram a b)
  let first := Procedure.ratMul.comp ((factorProgram a b).pair (Procedure.constant radialCode ratCode (shift a true)))
  let second := (shiftProgram b).comp inputCoefficientProgram
  let product := Procedure.ratMul.comp (first.pair second)
  exact (Procedure.ratSub.comp ((Procedure.ratAdd.comp (left.pair right)).pair product)).congrFun
    (by intro x; rfl)

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumExchangeSampleProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal evaluation of each cross-block physical exchange coefficient. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque stencilProgram (a : Fin 2) (p : Fin 4) : Procedure ratCode ratCode
    (fun t => stencil a (decide (t ≤ 0)) p) := by
  exact (Procedure.conditional positiveProgram (Procedure.constant ratCode ratCode (stencil a false p))
    (Procedure.constant ratCode ratCode (stencil a true p))).congrFun (by
      intro t
      by_cases ht : 0 < t
      · simp [ht,not_le_of_gt ht]
      · simp [ht,le_of_not_gt ht])

noncomputable opaque crossCouplingProgram (a b : Fin 2) : Procedure crossCode ratCode
    (fun x => calibrated a b (x.1.1,x.2)) :=
  (calibratedProgram a b).comp (crossPrecisionProgram.pair crossCoefficientProgram)

noncomputable opaque crossBaseProgram (a b : Fin 2) : Procedure crossCode ratCode
    (fun x => x.1.2*calibrated a b (x.1.1,x.2)) :=
  Procedure.ratMul.comp (crossScaleProgram.pair (crossCouplingProgram a b))

noncomputable opaque crossStencilProgram (a b : Fin 2) (p q : Fin 4) : Procedure crossCode ratCode
    (fun x => stencil a true p*stencil b (decide (x.2 ≤ 0)) q) :=
  Procedure.ratMul.comp ((Procedure.constant crossCode ratCode (stencil a true p)).pair
    ((stencilProgram b q).comp crossCoefficientProgram))

noncomputable opaque crossValueProgram (a b : Fin 2) (p q : Fin 4) : Procedure crossCode ratCode
    (fun x => crossValue x.1.1 x.1.2 a b x.2 p q) :=
  (Procedure.ratMul.comp ((crossBaseProgram a b).pair (crossStencilProgram a b p q))).congrFun
    (by intro x; rfl)

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial programs for fixed-size physical exchange instructions. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram ExactQuantumFactoring.BitStackProgram

noncomputable def fixedListProgram {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (m : ℕ) (f : Fin m → α → β) (p : ∀ i, Procedure ea eb (f i)) :
    Procedure ea (listCode eb) (fun x => List.ofFn (fun i => f i x)) := by
  induction m with
  | zero => exact (Procedure.constant ea (listCode eb) []).congrFun (by intro x; simp)
  | succ m ih =>
    exact ((Procedure.listCons eb).comp ((p 0).pair
      (ih (fun i => f i.succ) (fun i => p i.succ)))).congrFun (by
        intro x
        simp only [Function.comp_apply,List.ofFn_succ])

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

noncomputable def swapPrefixProgram :
    Procedure (prodCode unaryCode Nat.bits) (listCode gateCode)
      (fun x => swapPrefix x.2 x.1) := by
  let k := Procedure.unaryToBits.comp (Procedure.first unaryCode Nat.bits)
  let a := Procedure.second unaryCode Nat.bits
  let step := swapListProgram.comp (Procedure.binaryAdd.comp (a.pair k))
  let table := Procedure.tabulate (f := fun a k => swapList (a+k)) [] step
  exact ((QuantumRawExchange.flattenProgram gateCode (.hadamard 0)).comp table).congrFun
    (by intro x; rfl)

noncomputable def adjacentProgram :
    Procedure adjacentInputCode (listCode gateCode)
      (fun x => adjacentList x.2.1 x.1 x.2.2) := by
  let d := Procedure.first unaryCode (prodCode Nat.bits Procedure.boolCode)
  let ab := Procedure.second unaryCode (prodCode Nat.bits Procedure.boolCode)
  let a := (Procedure.first Nat.bits Procedure.boolCode).comp ab
  let b := (Procedure.second Nat.bits Procedure.boolCode).comp ab
  let p := swapPrefixProgram.comp (d.pair a)
  let left := Procedure.binaryAdd.comp (a.pair (Procedure.unaryToBits.comp d))
  let right := Procedure.successor.comp left
  let center := orderedCnotProgram.comp ((left.pair right).pair b)
  let singleton := (Procedure.listCons gateCode).comp
    (center.pair (Procedure.constant adjacentInputCode (listCode gateCode) []))
  let first := (Procedure.listAppend gateCode (.hadamard 0)).comp (p.pair singleton)
  exact (Procedure.listAppend gateCode (.hadamard 0)).comp
    (first.pair ((Procedure.listReverse gateCode (.hadamard 0)).comp p))

end ContinuumCoulomb.QuantumCircuitCode

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

def deltaCore (c : QMACircuit) (t : Fin c.gates.length) :
    Matrix (QMASupportBasis (qmaPropagationSites c t))
      (QMASupportBasis (qmaPropagationSites c t)) Scalar :=
  fun s r => delta c t (qmaSupportExtend _ s) (qmaSupportExtend _ r)

def propagationCore (c : QMACircuit) (t : Fin c.gates.length) :=
  matMul (adjoint (deltaCore c t)) (deltaCore c t)

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAlgebraicScalarProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial programs for the exact algebraic history scalars.
Each operation uses only rational arithmetic on four registers. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicScalar
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque realRatProgram : Procedure ratCode realCode realRat :=
  (Procedure.identity ratCode).pair (Procedure.constant ratCode ratCode 0)

noncomputable opaque realAddProgram : Procedure (prodCode realCode realCode) realCode
    (fun x => realAdd x.1 x.2) := by
  let l := Procedure.first realCode realCode
  let r := Procedure.second realCode realCode
  let a := (Procedure.first ratCode ratCode).comp l
  let b := (Procedure.second ratCode ratCode).comp l
  let c := (Procedure.first ratCode ratCode).comp r
  let d := (Procedure.second ratCode ratCode).comp r
  exact (Procedure.ratAdd.comp (a.pair c)).pair (Procedure.ratAdd.comp (b.pair d))

noncomputable opaque realNegProgram : Procedure realCode realCode realNeg :=
  (Procedure.ratNeg.comp (Procedure.first ratCode ratCode)).pair
    (Procedure.ratNeg.comp (Procedure.second ratCode ratCode))

noncomputable opaque realSubProgram : Procedure (prodCode realCode realCode) realCode
    (fun x => realSub x.1 x.2) :=
  realAddProgram.comp ((Procedure.first realCode realCode).pair
    (realNegProgram.comp (Procedure.second realCode realCode)))

noncomputable opaque realMulProgram : Procedure (prodCode realCode realCode) realCode
    (fun x => realMul x.1 x.2) := by
  let l := Procedure.first realCode realCode
  let r := Procedure.second realCode realCode
  let a := (Procedure.first ratCode ratCode).comp l
  let b := (Procedure.second ratCode ratCode).comp l
  let c := (Procedure.first ratCode ratCode).comp r
  let d := (Procedure.second ratCode ratCode).comp r
  let ac := Procedure.ratMul.comp (a.pair c)
  let bd := Procedure.ratMul.comp (b.pair d)
  let ad := Procedure.ratMul.comp (a.pair d)
  let bc := Procedure.ratMul.comp (b.pair c)
  let half := Procedure.ratDiv.comp
    (bd.pair (Procedure.constant (prodCode realCode realCode) ratCode 2))
  exact (Procedure.ratAdd.comp (ac.pair half)).pair (Procedure.ratAdd.comp (ad.pair bc))

noncomputable opaque ratProgram : Procedure ratCode scalarCode rat :=
  realRatProgram.pair (Procedure.constant ratCode realCode (realRat 0))

noncomputable opaque addProgram : Procedure (prodCode scalarCode scalarCode) scalarCode
    (fun x => add x.1 x.2) := by
  let l := Procedure.first scalarCode scalarCode
  let r := Procedure.second scalarCode scalarCode
  let re := Procedure.first realCode realCode
  let im := Procedure.second realCode realCode
  exact (realAddProgram.comp ((re.comp l).pair (re.comp r))).pair
    (realAddProgram.comp ((im.comp l).pair (im.comp r)))

noncomputable opaque negProgram : Procedure scalarCode scalarCode neg :=
  (realNegProgram.comp (Procedure.first realCode realCode)).pair
    (realNegProgram.comp (Procedure.second realCode realCode))

noncomputable opaque subProgram : Procedure (prodCode scalarCode scalarCode) scalarCode
    (fun x => sub x.1 x.2) :=
  addProgram.comp ((Procedure.first scalarCode scalarCode).pair
    (negProgram.comp (Procedure.second scalarCode scalarCode)))

noncomputable opaque mulProgram : Procedure (prodCode scalarCode scalarCode) scalarCode
    (fun x => mul x.1 x.2) := by
  let l := Procedure.first scalarCode scalarCode
  let r := Procedure.second scalarCode scalarCode
  let re := Procedure.first realCode realCode
  let im := Procedure.second realCode realCode
  let ac := realMulProgram.comp ((re.comp l).pair (re.comp r))
  let bd := realMulProgram.comp ((im.comp l).pair (im.comp r))
  let ad := realMulProgram.comp ((re.comp l).pair (im.comp r))
  let bc := realMulProgram.comp ((im.comp l).pair (re.comp r))
  exact (realSubProgram.comp (ac.pair bd)).pair (realAddProgram.comp (ad.pair bc))

noncomputable opaque conjProgram : Procedure scalarCode scalarCode conj :=
  (Procedure.first realCode realCode).pair
    (realNegProgram.comp (Procedure.second realCode realCode))

noncomputable opaque realPartProgram : Procedure scalarCode scalarCode realPart :=
  (Procedure.first realCode realCode).pair (Procedure.constant scalarCode realCode (realRat 0))

/-- Finite sums used by a fixed local matrix are bounded-depth compositions. -/
noncomputable def fixedSumProgram {α : Type} (ea : α → List Bool) (m : ℕ)
    (f : Fin m → α → Scalar) (p : ∀ i, Procedure ea scalarCode (f i)) :
    Procedure ea scalarCode (fun x => sum (List.ofFn (fun i => f i x))) := by
  induction m with
  | zero => exact (Procedure.constant ea scalarCode (rat 0)).congrFun (by intro x; rfl)
  | succ m ih =>
    exact (addProgram.comp ((p 0).pair
      (ih (fun i => f i.succ) (fun i => p i.succ)))).congrFun (by
        intro x
        simp only [List.ofFn_succ,sum,Function.comp_apply])

def sampleCode : (ℕ × RealScalar) → List Bool := prodCode unaryCode realCode

noncomputable opaque sampleProgram : Procedure sampleCode ratCode (fun x => sample x.1 x.2) := by
  let k := Procedure.first unaryCode realCode
  let x := Procedure.second unaryCode realCode
  let a := (Procedure.first ratCode ratCode).comp x
  let b := (Procedure.second ratCode ratCode).comp x
  let root := RationalSquareRoot.program.comp
    (k.pair (Procedure.constant sampleCode ratCode (1/2)))
  exact Procedure.ratAdd.comp (a.pair (Procedure.ratMul.comp (b.pair root)))

end ContinuumCoulomb.QuantumAlgebraicScalar

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRouteProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.qmaFineRoute_nat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial programs for the lattice route length and each route point. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRouteCode
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque distanceProgram : Procedure pairCode Nat.bits (fun x => Nat.dist x.1 x.2) := by
  let a := Procedure.first Nat.bits Nat.bits
  let b := Procedure.second Nat.bits Nat.bits
  exact Procedure.binaryAdd.comp ((Procedure.binarySub.comp (a.pair b)).pair
    (Procedure.binarySub.comp (b.pair a)))

noncomputable opaque axisProgram : Procedure axisCode Nat.bits (fun x => qmaAxisWalk x.1.1 x.1.2 x.2) :=
  (Procedure.conditional (Procedure.binaryLe.comp (axisStartProgram.pair axisEndProgram))
    (Procedure.binaryAdd.comp (axisStartProgram.pair axisCursorProgram))
    (Procedure.binarySub.comp (axisStartProgram.pair axisCursorProgram))).congrFun
    (by intro x; simp [qmaAxisWalk])

noncomputable opaque horizontalLengthProgram : Procedure routeCode Nat.bits
    (fun x => Nat.dist x.1.1.1 x.1.2.1) :=
  distanceProgram.comp (startXProgram.pair endXProgram)
noncomputable opaque verticalLengthProgram : Procedure routeCode Nat.bits
    (fun x => Nat.dist x.1.1.2 x.1.2.2) :=
  distanceProgram.comp (startYProgram.pair endYProgram)
noncomputable opaque lengthProgram : Procedure routeCode Nat.bits
    (fun x => qmaManhattanLength x.1.1 x.1.2) :=
  Procedure.binaryAdd.comp (horizontalLengthProgram.pair verticalLengthProgram)

noncomputable opaque horizontalPointProgram : Procedure routeCode Nat.bits
    (fun x => qmaAxisWalk x.1.1.1 x.1.2.1 x.2) :=
  axisProgram.comp ((startXProgram.pair endXProgram).pair cursorProgram)
noncomputable opaque verticalPointProgram : Procedure routeCode Nat.bits
    (fun x => qmaAxisWalk x.1.1.2 x.1.2.2 (x.2-Nat.dist x.1.1.1 x.1.2.1)) :=
  axisProgram.comp ((startYProgram.pair endYProgram).pair
    (Procedure.binarySub.comp (cursorProgram.pair horizontalLengthProgram)))

noncomputable opaque pointProgram : Procedure routeCode pairCode
    (fun x => qmaManhattanPoint x.1.1 x.1.2 x.2) :=
  (Procedure.conditional (Procedure.binaryLe.comp (cursorProgram.pair horizontalLengthProgram))
    (horizontalPointProgram.pair startYProgram) (endXProgram.pair verticalPointProgram)).congrFun
    (by intro x; simp [qmaManhattanPoint])

end ContinuumCoulomb.QuantumRouteCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedArmProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal evaluation and enumeration of the three buffered endpoint arms.
The lane color is unary, as required by the polynomial geometric size bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumBufferedArmProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable def add {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea Nat.bits f) (q : Procedure ea Nat.bits g) :
    Procedure ea Nat.bits (fun x => f x+g x) := Procedure.binaryAdd.comp (p.pair q)
noncomputable def mul {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea Nat.bits f) (q : Procedure ea Nat.bits g) :
    Procedure ea Nat.bits (fun x => f x*g x) := Procedure.binaryMul.comp (p.pair q)

noncomputable def doglegProgram : Procedure axisCode pairCode
    (fun x => qmaBufferedDoglegPoint x.1.1 x.1.2 x.2) :=
  (Procedure.conditional (le k (sub v (c 17))) ((add (c 17) k).pair (c 17))
    (Procedure.conditional (le k (add (sub v (c 17)) (sub u (c 17))))
      (v.pair (add (c 17) (sub k (sub v (c 17))))) (u.pair u))).congrFun (by
        intro x
        simp only [qmaBufferedDoglegPoint,decide_eq_true_eq])

noncomputable def detourProgram : Procedure axisCode pairCode
    (fun x => qmaBufferedDetourPoint x.1.1 x.1.2 x.2) :=
  (Procedure.conditional (le k (c 8)) ((sub (c 17) k).pair (c 17))
    (Procedure.conditional (le k u) ((c 9).pair (add k (c 9)))
      (Procedure.conditional (le k (sub (add u v) (c 9)))
        ((add (sub k u) (c 9)).pair (add u (c 9)))
        (Procedure.conditional (le k (add u v))
          (v.pair (sub (add (mul (c 2) u) v) k)) (u.pair u))))).congrFun (by
            intro x
            simp only [qmaBufferedDetourPoint,decide_eq_true_eq])

noncomputable def pointProgram (a : Fin 3) :
    Procedure (prodCode unaryCode Nat.bits) pairCode (fun x => point a x.1 x.2) := by
  let en := prodCode unaryCode Nat.bits
  let color := Procedure.unaryToBits.comp (Procedure.first unaryCode Nat.bits)
  let port := mul (Procedure.constant en Nat.bits 8)
    (add color (Procedure.constant en Nat.bits 3))
  let arg := (port.pair (sub port (Procedure.constant en Nat.bits 1))).pair
    (Procedure.second unaryCode Nat.bits)
  let dog := doglegProgram.comp arg
  by_cases ha : a=0
  · exact dog.congrFun (by intro x; simp [point,ha])
  · by_cases hb : a=1
    · exact (Procedure.swap Nat.bits Nat.bits |>.comp dog).congrFun (by
        intro x; simp [point,hb])
    · exact (detourProgram.comp arg).congrFun (by
        intro x; simp [point,ha,hb])

noncomputable def listProgram (a : Fin 3) : Procedure unaryCode (listCode pairCode)
    (fun color => (List.range (length a color+1)).map (point a color)) := by
  let step := (pointProgram a).comp ((Procedure.second unaryCode unaryCode).pair
    (Procedure.unaryToBits.comp (Procedure.first unaryCode unaryCode)))
  let all := Procedure.tabulate (0,0) step
  let n := Procedure.unarySuccessor.comp (lengthProgram a)
  exact all.comp (n.pair (Procedure.identity unaryCode))

end ContinuumCoulomb.QuantumBufferedArmProgram

end

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

theorem qmaFineRouteSites_nat {rows width A : ℕ} (p q : QMAFineGrid rows width A) (z : ℕ × ℕ) :
    qmaManhattanSupport (qmaFineGridNat p) (qmaFineGridNat q) z ↔
      ∃ w ∈ qmaFineRouteSites p q, qmaFineGridNat w = z := by
  constructor
  · intro hz
    obtain ⟨k,hk,he⟩ := qmaManhattanSupport_point hz
    refine ⟨qmaFineRoute p q ⟨k,by omega⟩,?_,?_⟩
    · exact Finset.mem_image.mpr ⟨⟨k,by omega⟩,Finset.mem_univ _,rfl⟩
    · exact he
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hw
    exact qmaManhattanPoint_support _ _ k.val (by omega)

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem lane_color_disjoint (hA : 0 < A) {e f : M.Term} (hef : e ≠ f)
    (hcolor : M.laneColor e = M.laneColor f) :
    Disjoint {z | M.laneSupport e z} {z | M.laneSupport f z} := by
  have hc : M.termSlots.color e = M.termSlots.color f :=
    (qmaGridColorEquiv B).injective hcolor
  have hd := M.routes_of_color_disjoint hA hef hc
  have hsupport : Disjoint
      {z | qmaManhattanSupport (qmaFineGridNat (M.routeLeft e)) (qmaFineGridNat (M.routeRight e)) z}
      {z | qmaManhattanSupport (qmaFineGridNat (M.routeLeft f)) (qmaFineGridNat (M.routeRight f)) z} := by
    apply Set.disjoint_left.mpr
    intro z he hf
    obtain ⟨u,hu,huz⟩ := (qmaFineRouteSites_nat _ _ z).mp he
    obtain ⟨v,hv,hvz⟩ := (qmaFineRouteSites_nat _ _ z).mp hf
    have huv := qmaFineGridNat_injective (huz.trans hvz.symm)
    subst v
    exact Finset.disjoint_left.mp hd hu hv
  change Disjoint {z | qmaLaneSupport (M.laneColor e) _ _ z}
    {z | qmaLaneSupport (M.laneColor f) _ _ z}
  rw [← hcolor]
  exact qmaLaneSupport_disjoint _ hsupport

end QMASpatialExchangeModel
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


namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem incident_color_injective (hA : 0 < A) (v : Fin M.n) :
    Function.Injective (fun e : M.Incident v => M.laneColor e.val) := by
  intro e f hef
  change M.laneColor e.val = M.laneColor f.val at hef
  by_contra h
  have hval : e.val ≠ f.val := fun hh => h (Subtype.ext hh)
  have he := M.incident_lane_support v e
  have hf := M.incident_lane_support v f
  rw [← hef] at hf
  exact Set.disjoint_left.mp (M.lane_color_disjoint hA hval hef) he hf

theorem endpointPorts_assign_injective (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (v : Fin M.n) :
    Function.Injective (M.endpointPorts hd v).assign := by
  intro e f hef
  apply M.incident_color_injective hA v
  apply Fin.ext
  have hh := congrArg Fin.val (congrArg (M.endpointPorts hd v).slot hef)
  simpa only [(M.endpointPorts hd v).aligned,Fin.val_castAdd] using hh

end QMASpatialExchangeModel
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

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem spaced_color_disjoint (hA : 0 < A) {e f : M.Term} (hef : e ≠ f)
    (hcolor : M.spacedColor e = M.spacedColor f) :
    Disjoint {z | M.spacedSupport e z} {z | M.spacedSupport f z} := by
  have hc := M.spacedColor_eq hcolor
  have hd := M.routes_of_color_disjoint hA hef ((qmaGridColorEquiv B).injective hc)
  have hs : Disjoint
      {z | qmaManhattanSupport (qmaFineGridNat (M.routeLeft e)) (qmaFineGridNat (M.routeRight e)) z}
      {z | qmaManhattanSupport (qmaFineGridNat (M.routeLeft f)) (qmaFineGridNat (M.routeRight f)) z} := by
    apply Set.disjoint_left.mpr
    intro z he hf
    obtain ⟨u,hu,huz⟩ := (qmaFineRouteSites_nat _ _ z).mp he
    obtain ⟨v,hv,hvz⟩ := (qmaFineRouteSites_nat _ _ z).mp hf
    have huv := qmaFineGridNat_injective (huz.trans hvz.symm)
    subst v
    exact Finset.disjoint_left.mp hd hu hv
  change Disjoint {z | qmaLaneSupport (M.spacedColor e) _ _ z}
    {z | qmaLaneSupport (M.spacedColor f) _ _ z}
  rw [← hcolor]
  exact qmaLaneSupport_disjoint _ hs

theorem spaced_crossing_not_vertex (hA : 0 < A) {e f : M.Term} (hef : e ≠ f)
    {z : ℕ × ℕ} (he : M.spacedSupport e z) (hf : M.spacedSupport f z)
    (g : M.Term) (p : ℕ × ℕ) : z ≠ qmaLanePoint (M.spacedColor g) p := by
  have hc : M.spacedColor e ≠ M.spacedColor f := fun h =>
    Set.disjoint_left.mp (M.spaced_color_disjoint hA hef h) he hf
  exact qmaLaneSupport_crossing_not_vertex hc he hf _ p

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedEndpointWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual unit-step walks join the degree-three vertices through their separated lanes. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def spacedWalk (e : M.Term) :
    qmaSquareGrid.Walk (qmaLanePoint (M.spacedColor e) (M.routeVertex (M.left e)))
      (qmaLanePoint (M.spacedColor e) (M.routeVertex (M.right e))) :=
  let p := qmaLanePoint (M.spacedColor e) (M.routeVertex (M.left e))
  let q := qmaLanePoint (M.spacedColor e) (M.routeVertex (M.right e))
  (qmaGridWalk (qmaManhattanPoint p q) (qmaManhattanLength p q)
    (qmaManhattanPoint_adj p q)).copy (qmaManhattanPoint_zero p q) (qmaManhattanPoint_last p q)

theorem spacedWalk_length (e : M.Term) : (M.spacedWalk e).length ≤ 8*(9*B+9)*(3*A+2) := by
  dsimp only [spacedWalk]
  rw [SimpleGraph.Walk.length_copy,qmaGridWalk_length]
  exact M.spaced_length e

def bufferedWalk (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    qmaSquareGrid.Walk (M.placedVertex (M.left e)) (M.placedVertex (M.right e)) :=
  ((M.endpointArmWalk hd (M.left e) ⟨e,Or.inl rfl⟩).append (M.spacedWalk e)).append
    (M.endpointArmWalk hd (M.right e) ⟨e,Or.inr rfl⟩).reverse

theorem bufferedWalk_length (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    (M.bufferedWalk hd e).length ≤ 2*(16*(9*B+6)+2)+8*(9*B+9)*(3*A+2) := by
  have hl := M.endpointArm_length_bound hd (M.left e) ⟨e,Or.inl rfl⟩
  have hr := M.endpointArm_length_bound hd (M.right e) ⟨e,Or.inr rfl⟩
  have hg := M.spacedWalk_length e
  simp only [bufferedWalk,SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse,
    endpointArmWalk_length]
  omega

def bufferedPath (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    qmaSquareGrid.Path (M.placedVertex (M.left e)) (M.placedVertex (M.right e)) :=
  (M.bufferedWalk hd e).toPath

theorem bufferedPath_length (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    (M.bufferedPath hd e).val.length ≤ 2*(16*(9*B+6)+2)+8*(9*B+9)*(3*A+2) :=
  ((M.bufferedWalk hd e).length_bypass_le_length).trans (M.bufferedWalk_length hd e)

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The routed paths visit original graph vertices only at their own endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem spacedWalk_support (e : M.Term) {z : ℕ × ℕ}
    (hz : z ∈ (M.spacedWalk e).support) : M.spacedSupport e z := by
  simp only [spacedWalk,SimpleGraph.Walk.support_copy] at hz
  obtain ⟨k,hk,he⟩ := qmaGridWalk_support _ _ _ hz
  rw [← he]
  exact qmaManhattanPoint_support _ _ k hk

theorem bufferedPath_support (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) {z : ℕ × ℕ} (hz : z ∈ (M.bufferedPath hd e).val.support) :
    M.endpointArmSupport hd (M.left e) ⟨e,Or.inl rfl⟩ z ∨ M.spacedSupport e z ∨
      M.endpointArmSupport hd (M.right e) ⟨e,Or.inr rfl⟩ z := by
  have h := (M.bufferedWalk hd e).support_toPath_subset_support hz
  simp only [bufferedWalk,SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_reverse,List.mem_reverse] at h
  rcases h with (h | h) | h
  · exact Or.inl (M.endpointArmWalk_support hd _ _ h)
  · exact Or.inr (Or.inl (M.spacedWalk_support e h))
  · exact Or.inr (Or.inr (M.endpointArmWalk_support hd _ _ h))

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Buffered routes lie strictly inside the nonnegative lattice quadrant. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem bufferedPath_positive (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) {z : ℕ × ℕ} (hz : z ∈ (M.bufferedPath hd e).val.support) :
    0 < z.1 ∧ 0 < z.2 := by
  rcases M.bufferedPath_support hd e hz with h | h | h
  · exact M.endpointArmSupport_positive hd _ _ h
  · exact M.spacedSupport_positive e h
  · exact M.endpointArmSupport_positive hd _ _ h

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedIntersections
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.exchangeGraph_energy _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_energy _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_qubit_index _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_term_index _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Buffered arms are mutually disjoint away from their common graph vertex. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem endpointArmSupport_meet (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v w : Fin M.n) (e : M.Incident v) (f : M.Incident w) {z : ℕ × ℕ}
    (he : M.endpointArmSupport hd v e z) (hf : M.endpointArmSupport hd w f z) :
    e.val = f.val ∨ z = M.placedVertex v := by
  obtain ⟨p,hp,hps⟩ := he
  obtain ⟨q,hq,hqs⟩ := hf
  have hpb := M.endpointLocal_bounds hd v _ hps
  have hqb := M.endpointLocal_bounds hd w _ hqs
  have heq := hp.trans hq.symm
  have hvw : v = w := by
    apply M.routeVertex_injective
    by_contra hn
    exact qmaBufferedCellPoint_disjoint hn ⟨hpb.2.1,hpb.2.2.2⟩ ⟨hqb.2.1,hqb.2.2.2⟩ heq
  subst w
  have hpq := qmaBufferedCellPoint_injective (9*B+3) (M.routeVertex v) heq
  subst q
  by_cases hef : e.val = f.val
  · exact Or.inl hef
  · have ha : (M.endpointPorts hd v).assign e ≠ (M.endpointPorts hd v).assign f := by
      intro h
      exact hef (congrArg Subtype.val (M.endpointPorts_assign_injective hA hd v h))
    have hc := qmaBufferedFanout_only_center (M.endpointColors hd v)
      ((M.endpointPorts hd v).increasing (show (0 : Fin 3) < 1 by decide))
      ((M.endpointPorts hd v).increasing (show (1 : Fin 3) < 2 by decide))
      (fun _ => false) ha hps hqs
    exact Or.inr (hp.symm.trans (congrArg (qmaBufferedCellPoint (9*B+3) (M.routeVertex v)) hc))

theorem spaced_crossing_grid (hA : 0 < A) {e f : M.Term} (hef : e ≠ f)
    {z : ℕ × ℕ} (he : M.spacedSupport e z) (hf : M.spacedSupport f z) :
    z.1 % 8 = 0 ∧ z.2 % 8 = 0 := by
  have hc : M.spacedColor e ≠ M.spacedColor f := fun h =>
    Set.disjoint_left.mp (M.spaced_color_disjoint hA hef h) he hf
  rcases qmaLaneSupport_transverse hc he hf with ⟨hy,hx⟩ | ⟨hx,hy⟩
  all_goals
    constructor
    · rw [hx]
      simp [spacedColor,qmaSpacedLaneColor,Nat.add_mod,Nat.mul_mod]
    · rw [hy]
      simp [spacedColor,qmaSpacedLaneColor,Nat.add_mod,Nat.mul_mod]

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedSharedEdge
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.exchangeGraph_energy _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_energy _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_qubit_index _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_term_index _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Different routes do not share lattice edges, including at buffered endpoint cells. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem arm_lane_not_grid (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) {f : M.Term} (hef : e.val ≠ f) {p : ℕ × ℕ}
    (he : M.endpointArmSupport hd v e p) (hf : M.spacedSupport f p) :
    ¬(p.1 % 8 = 0 ∧ p.2 % 8 = 0) := by
  intro hp
  have ht := M.endpointArmSupport_grid hd v e he hp
  have hg : M.spacedSupport e.val p := by rw [ht]; exact M.spaced_incident_support v e
  exact M.spaced_crossing_not_vertex hA hef hg hf e.val (M.routeVertex v) ht

theorem endpointArm_lane_no_edge (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) {f : M.Term} (hef : e.val ≠ f) {p q : ℕ × ℕ}
    (hp : M.endpointArmSupport hd v e p) (hq : M.endpointArmSupport hd v e q)
    (hpf : M.spacedSupport f p) (hqf : M.spacedSupport f q) (ha : qmaSquareGrid.Adj p q) : False := by
  obtain ⟨r,hr,hrs⟩ := hp
  obtain ⟨s,hs,hss⟩ := hq
  have har : qmaSquareGrid.Adj r s := by
    rw [← hr,← hs] at ha
    simpa only [qmaSquareGrid,qmaBufferedCellPoint,Nat.dist_add_add_left] using ha
  rcases M.spaced_unit_direction f hpf hqf ha with ⟨hxy,hm⟩ | ⟨hxy,hm⟩
  · have hx : r.1 = s.1 := by
      have h := congrArg Prod.fst hr
      have h' := congrArg Prod.fst hs
      dsimp [qmaBufferedCellPoint] at h h'
      omega
    have hm' : r.1 % 8 = 0 := by
      have h := congrArg (fun x : ℕ × ℕ => x.1 % 8) hr
      simpa [qmaBufferedCellPoint,Nat.add_mod,Nat.mul_mod,hm] using h
    have hd' : Nat.dist r.2 s.2 = 1 := by simpa [qmaSquareGrid,hx] using har
    rcases qmaBufferedFanout_vertical_grid_edge _ _ hrs hss hx hm' hd' with ht | ht
    · apply M.arm_lane_not_grid hA hd v e hef ⟨r,hr,hrs⟩ hpf
      simp [← hr,qmaBufferedCellPoint,Nat.add_mod,Nat.mul_mod,hm',ht]
    · apply M.arm_lane_not_grid hA hd v e hef ⟨s,hs,hss⟩ hqf
      simp [← hs,qmaBufferedCellPoint,Nat.add_mod,Nat.mul_mod,← hx,hm',ht]
  · have hy : r.2 = s.2 := by
      have h := congrArg Prod.snd hr
      have h' := congrArg Prod.snd hs
      dsimp [qmaBufferedCellPoint] at h h'
      omega
    have hm' : r.2 % 8 = 0 := by
      have h := congrArg (fun x : ℕ × ℕ => x.2 % 8) hr
      simpa [qmaBufferedCellPoint,Nat.add_mod,Nat.mul_mod,hm] using h
    have hd' : Nat.dist r.1 s.1 = 1 := by simpa [qmaSquareGrid,hy] using har
    rcases qmaBufferedFanout_horizontal_grid_edge _ _ hrs hss hy hm' hd' with ht | ht
    · apply M.arm_lane_not_grid hA hd v e hef ⟨r,hr,hrs⟩ hpf
      simp [← hr,qmaBufferedCellPoint,Nat.add_mod,Nat.mul_mod,hm',ht]
    · apply M.arm_lane_not_grid hA hd v e hef ⟨s,hs,hss⟩ hqf
      simp [← hs,qmaBufferedCellPoint,Nat.add_mod,Nat.mul_mod,← hy,hm',ht]


theorem bufferedPath_edge_piece (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) {p q : ℕ × ℕ} (he : s(p,q) ∈ (M.bufferedPath hd e).val.edges) :
    (∃ (v : Fin M.n) (h : M.left e = v ∨ M.right e = v),
      M.endpointArmSupport hd v ⟨e,h⟩ p ∧ M.endpointArmSupport hd v ⟨e,h⟩ q) ∨
      (M.spacedSupport e p ∧ M.spacedSupport e q) := by
  have h := (M.bufferedWalk hd e).edges_toPath_subset_edges he
  simp only [bufferedWalk,SimpleGraph.Walk.edges_append,SimpleGraph.Walk.edges_reverse,
    List.mem_append,List.mem_reverse] at h
  rcases h with (h | h) | h
  · exact Or.inl ⟨M.left e,Or.inl rfl,
      M.endpointArmWalk_support hd _ _ ((M.endpointArmWalk hd _ _).fst_mem_support_of_mem_edges h),
      M.endpointArmWalk_support hd _ _ ((M.endpointArmWalk hd _ _).snd_mem_support_of_mem_edges h)⟩
  · exact Or.inr ⟨M.spacedWalk_support e ((M.spacedWalk e).fst_mem_support_of_mem_edges h),
      M.spacedWalk_support e ((M.spacedWalk e).snd_mem_support_of_mem_edges h)⟩
  · exact Or.inl ⟨M.right e,Or.inr rfl,
      M.endpointArmWalk_support hd _ _ ((M.endpointArmWalk hd _ _).fst_mem_support_of_mem_edges h),
      M.endpointArmWalk_support hd _ _ ((M.endpointArmWalk hd _ _).snd_mem_support_of_mem_edges h)⟩

theorem bufferedPath_no_shared_edge (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) {e f : M.Term} (hef : e ≠ f)
    {p q : ℕ × ℕ} (he : s(p,q) ∈ (M.bufferedPath hd e).val.edges)
    (hf : s(p,q) ∈ (M.bufferedPath hd f).val.edges) : False := by
  have ha := (M.bufferedPath hd e).val.adj_of_mem_edges he
  rcases M.bufferedPath_edge_piece hd e he with ⟨v,hv,hpe,hqe⟩ | ⟨hpe,hqe⟩ <;>
    rcases M.bufferedPath_edge_piece hd f hf with ⟨w,hw,hpf,hqf⟩ | ⟨hpf,hqf⟩
  · have hp := M.endpointArmSupport_meet hA hd v w ⟨e,hv⟩ ⟨f,hw⟩ hpe hpf
    have hq := M.endpointArmSupport_meet hA hd v w ⟨e,hv⟩ ⟨f,hw⟩ hqe hqf
    have hp' : p = M.placedVertex v := hp.resolve_left hef
    have hq' : q = M.placedVertex v := hq.resolve_left hef
    rw [hp',hq'] at ha
    exact qmaSquareGrid.irrefl ha
  · exact M.endpointArm_lane_no_edge hA hd v ⟨e,hv⟩ hef hpe hqe hpf hqf ha
  · exact M.endpointArm_lane_no_edge hA hd w ⟨f,hw⟩ hef.symm hpf hqf hpe hqe ha
  · exact qmaSquareGrid_not_eightfold (M.spaced_crossing_grid hA hef hpe hpf)
      (M.spaced_crossing_grid hA hef hqe hqf) ha

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial rational programs for the crossing coefficients and penalty. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingCode
open ExactQuantumFactoring.BitStackProgram

noncomputable def squareProgram {α : Type} {ea : α → List Bool} {f : α → ℚ}
    (p : Procedure ea ratCode f) : Procedure ea ratCode (fun x => (f x)^2) :=
  (Procedure.ratMul.comp (p.pair p)).congrFun (by intro x; dsimp; ring)

noncomputable def twiceProductProgram {α : Type} {ea : α → List Bool} {f g : α → ℚ}
    (p : Procedure ea ratCode f) (q : Procedure ea ratCode g) :
    Procedure ea ratCode (fun x => 2*f x*g x) :=
  Procedure.ratMul.comp ((Procedure.ratMul.comp
    ((Procedure.constant ea ratCode 2).pair p)).pair q)

noncomputable opaque sumPlusOneProgram : Procedure tripleCode ratCode
    (fun x => x.1+x.2.1+1) :=
  Procedure.ratAdd.comp ((Procedure.ratAdd.comp (firstProgram.pair secondProgram)).pair
    (Procedure.constant tripleCode ratCode 1))

noncomputable opaque cubeProgram : Procedure tripleCode ratCode (fun x => (x.1+x.2.1+1)^3) :=
  (Procedure.ratMul.comp ((squareProgram sumPlusOneProgram).pair sumPlusOneProgram)).congrFun
    (by intro x; dsimp; ring)

noncomputable opaque scaleProgram : Procedure tripleCode ratCode
    (fun x => 16*(x.1+x.2.1+1)^3*x.2.2+4*(x.1+x.2.1+1)+1) := by
  let leading := Procedure.ratMul.comp ((Procedure.ratMul.comp
    ((Procedure.constant tripleCode ratCode 16).pair cubeProgram)).pair thirdProgram)
  let lower := Procedure.ratMul.comp ((Procedure.constant tripleCode ratCode 4).pair sumPlusOneProgram)
  exact Procedure.ratAdd.comp ((Procedure.ratAdd.comp (leading.pair lower)).pair
    (Procedure.constant tripleCode ratCode 1))

noncomputable opaque offsetProgram : Procedure tripleCode ratCode
    (fun x => 3/2+3*x.2.1^2+3*x.2.2^2) := by
  let j := Procedure.ratMul.comp ((Procedure.constant tripleCode ratCode 3).pair (squareProgram secondProgram))
  let k := Procedure.ratMul.comp ((Procedure.constant tripleCode ratCode 3).pair (squareProgram thirdProgram))
  exact Procedure.ratAdd.comp ((Procedure.ratAdd.comp
    ((Procedure.constant tripleCode ratCode (3/2)).pair j)).pair k)

noncomputable opaque coefficientProgram (k : Fin 10) :
    Procedure tripleCode ratCode (fun x => coefficients x k) := by
  by_cases h0 : k = 0
  · subst k
    exact (squareProgram firstProgram).congrFun (by intro x; rfl)
  by_cases h1 : k = 1
  · subst k
    exact firstProgram.congrFun (by intro x; rfl)
  by_cases h2 : k = 2
  · subst k
    exact firstProgram.congrFun (by intro x; rfl)
  by_cases h3 : k = 3
  · subst k
    exact (twiceProductProgram firstProgram secondProgram).congrFun (by intro x; rfl)
  by_cases h4 : k = 4
  · subst k
    exact (twiceProductProgram firstProgram thirdProgram).congrFun (by intro x; rfl)
  by_cases h5 : k = 5
  · subst k
    exact (Procedure.constant tripleCode ratCode (1/2)).congrFun (by intro x; rfl)
  by_cases h6 : k = 6
  · subst k
    exact (Procedure.ratNeg.comp thirdProgram).congrFun (by intro x; rfl)
  by_cases h7 : k = 7
  · subst k
    exact (Procedure.ratNeg.comp secondProgram).congrFun (by intro x; rfl)
  by_cases h8 : k = 8
  · subst k
    exact (twiceProductProgram secondProgram thirdProgram).congrFun (by intro x; rfl)
  have h9 : k = 9 := by omega
  subst k
  exact (Procedure.ratAdd.comp (offsetProgram.pair
      (Procedure.ratMul.comp ((Procedure.constant tripleCode ratCode 3).pair
        (squareProgram firstProgram))))).congrFun (by intro x; rfl)

end ContinuumCoulomb.QuantumRoutingCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedPortChain
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_energy _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_qubit_index _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_term_index _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual bounded spatial routes give distinct physical spin locations at every
cell port, including cells at which two coarse routes cross. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def coarseRoute (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) (i : ℕ) : ℕ × ℕ :=
  (M.bufferedPath hd e).val.getVert i

def coarseLength (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) : ℕ :=
  (M.bufferedPath hd e).val.length

theorem coarseLength_pos (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    0 < M.coarseLength hd e := by
  by_contra h
  have hz : (M.bufferedPath hd e).val.length = 0 := by exact Nat.eq_zero_of_not_pos h
  have he := (M.bufferedPath hd e).val.getVert_length
  rw [hz,SimpleGraph.Walk.getVert_zero] at he
  exact M.distinct e (M.placedVertex_injective he)

@[simp] theorem coarseRoute_zero (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    M.coarseRoute hd e 0 = M.placedVertex (M.left e) := SimpleGraph.Walk.getVert_zero _

@[simp] theorem coarseRoute_last (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    M.coarseRoute hd e (M.coarseLength hd e) = M.placedVertex (M.right e) :=
  SimpleGraph.Walk.getVert_length _

theorem coarseRoute_step (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term)
    (i : ℕ) (hi : i < M.coarseLength hd e) :
    qmaSquareGrid.Adj (M.coarseRoute hd e i) (M.coarseRoute hd e (i+1)) :=
  qmaGridPath_getVert_step (M.bufferedPath hd e) ⟨i,hi⟩

theorem coarseRoute_positive (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) (i : ℕ) : 0 < (M.coarseRoute hd e i).1 ∧ 0 < (M.coarseRoute hd e i).2 :=
  M.bufferedPath_positive hd e ((M.bufferedPath hd e).val.getVert_mem_support i)

theorem coarseRoute_simple (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) (i j : ℕ) (hi : i ≤ M.coarseLength hd e) (hj : j ≤ M.coarseLength hd e)
    (he : M.coarseRoute hd e i = M.coarseRoute hd e j) : i = j :=
  (M.bufferedPath hd e).property.getVert_injOn hi hj he

theorem coarseRoute_edges_disjoint (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) {e f : M.Term} (hef : e ≠ f)
    (i j : ℕ) (hi : i < M.coarseLength hd e) (hj : j < M.coarseLength hd f) :
    ¬(M.coarseRoute hd e i = M.coarseRoute hd f j ∧
        M.coarseRoute hd e (i+1) = M.coarseRoute hd f (j+1)) ∧
      ¬(M.coarseRoute hd e i = M.coarseRoute hd f (j+1) ∧
        M.coarseRoute hd e (i+1) = M.coarseRoute hd f j) := by
  have he : s(M.coarseRoute hd e i,M.coarseRoute hd e (i+1)) ∈ (M.bufferedPath hd e).val.edges :=
    ((M.bufferedPath hd e).val.mk_mem_edges_iff_exists).mpr ⟨i,hi,rfl⟩
  have hf : s(M.coarseRoute hd f j,M.coarseRoute hd f (j+1)) ∈ (M.bufferedPath hd f).val.edges :=
    ((M.bufferedPath hd f).val.mk_mem_edges_iff_exists).mpr ⟨j,hj,rfl⟩
  constructor
  · rintro ⟨h1,h2⟩
    rw [h1,h2] at he
    exact M.bufferedPath_no_shared_edge hA hd hef he hf
  · rintro ⟨h1,h2⟩
    rw [h1,h2,Sym2.eq_swap] at he
    exact M.bufferedPath_no_shared_edge hA hd hef he hf

def portGraph (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) : SimpleGraph (ℕ × ℕ) :=
  SimpleGraph.fromRel (fun x y => ∃ (e : M.Term) (k : ℕ), k < 2*M.coarseLength hd e+1 ∧
    qmaPortChain (M.coarseRoute hd e) (M.coarseLength hd e) k = x ∧
    qmaPortChain (M.coarseRoute hd e) (M.coarseLength hd e) (k+1) = y)

def portRouteData (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) :
    QMAPortRouteData M.exchangeGraph where
  length := M.coarseLength hd
  length_pos := M.coarseLength_pos hd
  position := M.placedVertex
  position_injective := M.placedVertex_injective
  point := M.coarseRoute hd
  first := M.coarseRoute_zero hd
  last := M.coarseRoute_last hd
  simple := M.coarseRoute_simple hd
  step := M.coarseRoute_step hd
  positive := fun e i _ => M.coarseRoute_positive hd e i
  edges_disjoint := fun _e _f hef => M.coarseRoute_edges_disjoint hA hd hef

def portEmbedding (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) :=
  (M.portRouteData hA hd).toEmbedding

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFiniteMembership
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal membership tests for the finite geometry tables used by the
140-candidate planar route selector. The Boolean fold has constant-size state. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFiniteMembership
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable def memberProgram {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
    (ea : α → List Bool)
    (d : α) (eqp : Procedure (prodCode ea ea) Procedure.boolCode (fun x => decide (x.1=x.2))) :
    Procedure (prodCode ea (listCode ea)) Procedure.boolCode
      (fun x => decide (x.1 ∈ x.2)) :=
  (anyProgram.comp (Procedure.listMapWith (f := fun a b => decide (a=b)) d false eqp)).congrFun (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp)

noncomputable opaque pairMemberProgram :
    Procedure (prodCode pairCode (listCode pairCode)) Procedure.boolCode
      (fun x => decide (x.1 ∈ x.2)) := memberProgram pairCode (0,0) pairEqProgram

end ContinuumCoulomb.QuantumFiniteMembership

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWalkSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual buffered walk is a finite list of explicit arm and Manhattan
points. Loop erasure therefore computes the path used by the port geometry. -/

noncomputable section
namespace ContinuumCoulomb

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def endpointArmList (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) : List (ℕ × ℕ) :=
  (List.range (M.endpointArmLength hd v e+1)).map (M.endpointArmPoint hd v e)

def spacedList (e : M.Term) : List (ℕ × ℕ) :=
  let p := qmaLanePoint (M.spacedColor e) (M.routeVertex (M.left e))
  let q := qmaLanePoint (M.spacedColor e) (M.routeVertex (M.right e))
  (List.range (qmaManhattanLength p q+1)).map (qmaManhattanPoint p q)

def bufferedList (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) : List (ℕ × ℕ) :=
  M.endpointArmList hd (M.left e) ⟨e,Or.inl rfl⟩ ++ (M.spacedList e).tail ++
    (M.endpointArmList hd (M.right e) ⟨e,Or.inr rfl⟩).reverse.tail

end QMASpatialExchangeModel
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
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable def armProgram : Procedure armCode (listCode pairCode) armList := by
  let a := Procedure.unaryToBits.comp (Procedure.first unaryCode unaryCode)
  let color := Procedure.second unaryCode unaryCode
  let is (k : ℕ) := Procedure.binaryEq.comp (a.pair (Procedure.constant armCode Nat.bits k))
  let branch (k : Fin 3) := (QuantumBufferedArmProgram.listProgram k).comp color
  exact (Procedure.conditional (is 0) (branch 0)
    (Procedure.conditional (is 1) (branch 1) (branch 2))).congrFun (by
      intro x
      simp only [Function.comp_apply,decide_eq_true_eq,armList,id_eq])

noncomputable def translateProgram (B : ℕ) : Procedure (prodCode pairCode pairCode) pairCode
    (fun x => translate B x.1 x.2) := by
  let p := Procedure.first pairCode pairCode
  let z := Procedure.second pairCode pairCode
  let coord (take : Procedure pairCode Nat.bits Prod.fst) :=
    Procedure.binaryAdd.comp
      ((Procedure.binaryMul.comp ((Procedure.constant _ Nat.bits (8*(9*B+3+6))).pair
        (take.comp p))).pair (take.comp z))
  let y := Procedure.binaryAdd.comp
    ((Procedure.binaryMul.comp ((Procedure.constant _ Nat.bits (8*(9*B+3+6))).pair
      ((Procedure.second Nat.bits Nat.bits).comp p))).pair
        ((Procedure.second Nat.bits Nat.bits).comp z))
  exact (coord (Procedure.first Nat.bits Nat.bits)).pair y

noncomputable def program (B : ℕ) : Procedure inputCode (listCode pairCode) (value B) :=
  (Procedure.listMapWith (f := translate B) (0,0) (0,0) (translateProgram B)).comp
    ((Procedure.first pairCode armCode).pair
      (armProgram.comp (Procedure.second pairCode armCode)))

end ContinuumCoulomb.QuantumEndpointListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumManhattanListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerate the Manhattan segment with an explicit fixed route budget.
The cap makes enumeration polynomial on every input, and disappears for
the spatial routes satisfying the proved length bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumManhattanListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable def distanceProgram : Procedure endsCode Nat.bits
    (fun x => qmaManhattanLength x.1 x.2) :=
  QuantumRouteCode.lengthProgram.comp
    ((Procedure.identity endsCode).pair (Procedure.constant endsCode Nat.bits 0))

noncomputable def program (K : ℕ) : Procedure endsCode (listCode pairCode) (value K) := by
  let length := Procedure.clippedUnary.comp
    ((Procedure.constant endsCode unaryCode K).pair distanceProgram)
  let point := QuantumRouteCode.pointProgram.comp
    ((Procedure.second unaryCode endsCode).pair
      (Procedure.unaryToBits.comp (Procedure.first unaryCode endsCode)))
  exact (Procedure.tabulate (f := fun x i => qmaManhattanPoint x.1 x.2 i) (0,0) point).comp
    ((Procedure.unarySuccessor.comp length).pair (Procedure.identity endsCode))

end ContinuumCoulomb.QuantumManhattanListProgram

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
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable def pointProgram (B : ℕ) : Procedure pointCode pairCode
    (fun x => point B x.1 x.2) := by
  let color := Procedure.unaryToBits.comp (Procedure.first unaryCode pairCode)
  let port := Procedure.binaryMul.comp ((Procedure.constant pointCode Nat.bits 8).pair
    (Procedure.binaryAdd.comp (color.pair (Procedure.constant pointCode Nat.bits 3))))
  exact (QuantumEndpointListProgram.translateProgram B).comp
    ((Procedure.second unaryCode pairCode).pair (port.pair port))

noncomputable def program (A B : ℕ) : Procedure inputCode (listCode pairCode) (value A B) := by
  let color := Procedure.first unaryCode (prodCode pairCode pairCode)
  let ends := Procedure.second unaryCode (prodCode pairCode pairCode)
  let left := (pointProgram B).comp (color.pair ((Procedure.first pairCode pairCode).comp ends))
  let right := (pointProgram B).comp (color.pair ((Procedure.second pairCode pairCode).comp ends))
  exact (QuantumManhattanListProgram.program (budget A B)).comp (left.pair right)

end ContinuumCoulomb.QuantumSpacedListProgram

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

noncomputable def stepProgram (ea : α → List Bool) (d : α)
    (eqp : Procedure (prodCode ea ea) Procedure.boolCode (fun x => decide (x.1=x.2))) :
    Procedure (prodCode ea (listCode ea)) (listCode ea) (fun x => step x.1 x.2) :=
  (Procedure.conditional (QuantumFiniteMembership.memberProgram ea d eqp)
    (QuantumWalkSeek.program ea d eqp) (Procedure.listCons ea)).congrFun (by
      intro x
      simp only [step,decide_eq_true_eq])

theorem fold_code_bound (ea : α → List Bool) (xs bs : List α) :
    (listCode ea (xs.foldl (fun ys a => step a ys) bs)).length ≤
      (listCode ea xs).length+(listCode ea bs).length := by
  have h := listCode_length_sublist ea (fold_sublist xs bs)
  have ha := listCode_length_append ea xs.reverse bs
  rw [listCode_length_rev] at ha
  omega

noncomputable def foldProgram (ea : α → List Bool) (d : α)
    (eqp : Procedure (prodCode ea ea) Procedure.boolCode (fun x => decide (x.1=x.2))) :
    Procedure (prodCode (listCode ea) (listCode ea)) (listCode ea)
      (fun x => x.1.foldl (fun ys a => step a ys) x.2) :=
  Procedure.foldList d (stepProgram ea d eqp) Polynomial.X (by
    intro xs bs i
    have h := fold_code_bound ea (xs.take i) bs
    have ht := listCode_length_take_le ea i xs
    simp only [Polynomial.eval_X]
    omega)

noncomputable def program (ea : α → List Bool) (d : α)
    (eqp : Procedure (prodCode ea ea) Procedure.boolCode (fun x => decide (x.1=x.2))) :
    Procedure (listCode ea) (listCode ea) erase :=
  ((foldProgram ea d eqp).comp ((Procedure.listReverse ea d).pair
    (Procedure.constant (listCode ea) (listCode ea) []))).congrFun (by
      intro xs
      simp only [Function.comp_apply,List.foldl_reverse,erase])

noncomputable def cellProgram :
    Procedure (listCode QuantumRouteCode.pairCode) (listCode QuantumRouteCode.pairCode)
      (erase : List (ℕ × ℕ) → List (ℕ × ℕ)) :=
  program QuantumRouteCode.pairCode (0,0) QuantumFiniteMembership.pairEqProgram

end ContinuumCoulomb.QuantumWalkErasure

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal construction and loop erasure of the complete buffered route.
The input consists of two computed fine-grid endpoints, one lane color and
the two computed incident port ranks. -/

noncomputable section
namespace ContinuumCoulomb.QuantumBufferedListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable def program (A B : ℕ) : Procedure inputCode (listCode pairCode) (value A B) := by
  let ends := Procedure.first (prodCode pairCode pairCode) (prodCode unaryCode (prodCode unaryCode unaryCode))
  let nums := Procedure.second (prodCode pairCode pairCode) (prodCode unaryCode (prodCode unaryCode unaryCode))
  let left := (Procedure.first pairCode pairCode).comp ends
  let right := (Procedure.second pairCode pairCode).comp ends
  let lane := (Procedure.first unaryCode (prodCode unaryCode unaryCode)).comp nums
  let ports := (Procedure.second unaryCode (prodCode unaryCode unaryCode)).comp nums
  let la := (Procedure.first unaryCode unaryCode).comp ports
  let ra := (Procedure.second unaryCode unaryCode).comp ports
  let leftArm := (QuantumEndpointListProgram.program B).comp (left.pair (la.pair lane))
  let rightArm := (QuantumEndpointListProgram.program B).comp (right.pair (ra.pair lane))
  let middle := (Procedure.listTail pairCode).comp
    ((QuantumSpacedListProgram.program A B).comp (lane.pair (left.pair right)))
  let last := (Procedure.listTail pairCode).comp ((Procedure.listReverse pairCode (0,0)).comp rightArm)
  let append := Procedure.listAppend pairCode (0,0)
  exact append.comp ((append.comp (leftArm.pair middle)).pair last)

def actualInput {A B : ℕ} (M : QMASpatialExchangeModel A B)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) : Input :=
  ((M.routeVertex (M.left e),M.routeVertex (M.right e)),
    (M.laneColor e).val,
    ((M.endpointPorts hd (M.left e)).assign ⟨e,Or.inl rfl⟩).val,
    ((M.endpointPorts hd (M.right e)).assign ⟨e,Or.inr rfl⟩).val)

noncomputable def pathProgram (A B : ℕ) : Procedure inputCode (listCode pairCode) (path A B) :=
  QuantumWalkErasure.cellProgram.comp (program A B)

end ContinuumCoulomb.QuantumBufferedListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRationalCrossing
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathSchedule.mem_active _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.mem_crossingCells _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simultaneous crossing-removal layer as exact rational ordinary-spin data. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph Matrix
open scoped BigOperators Classical

namespace QMARationalCrossingLayer
variable {r : ℕ}

def source (C : QMARationalCrossingLayer r) : QMARationalExchangeGraph where
  n := C.base.n
  Edge := C.base.Edge ⊕ (Fin r × Fin 2)
  left := Sum.elim C.base.left (fun p => C.site p.1 (if p.2 = 0 then 0 else 1))
  right := Sum.elim C.base.right (fun p => C.site p.1 (if p.2 = 0 then 2 else 3))
  distinct := by
    intro e
    rcases e with e | ⟨i,a⟩
    · exact C.base.distinct e
    · intro h
      have h' := C.injective i h
      fin_cases a <;> norm_num [Fin.ext_iff] at h'
  weight := Sum.elim C.base.weight (fun p => if p.2 = 0 then C.J p.1 else C.K p.1)
  constant := C.base.constant

end QMARationalCrossingLayer
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCellPathProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal rational-register-free programs evaluate all four finite cell path
families, including the two translated halves of an external corridor. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCellPathProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

def translateCode : TranslateInput → List Bool := prodCode pairCode pairCode

noncomputable opaque translateProgram : Procedure translateCode pairCode
    (fun x => qmaCellTranslate x.1 x.2) := by
  let p := Procedure.first pairCode pairCode
  let z := Procedure.second pairCode pairCode
  let px := (Procedure.first Nat.bits Nat.bits).comp p
  let py := (Procedure.second Nat.bits Nat.bits).comp p
  let zx := (Procedure.first Nat.bits Nat.bits).comp z
  let zy := (Procedure.second Nat.bits Nat.bits).comp z
  let c := Procedure.constant translateCode Nat.bits 32
  let x := Procedure.binaryAdd.comp ((Procedure.binaryMul.comp (c.pair px)).pair zx)
  let y := Procedure.binaryAdd.comp ((Procedure.binaryMul.comp (c.pair py)).pair zy)
  exact (x.pair y).congrFun (by intro x; rfl)

noncomputable opaque translatedPathProgram (xs : List Pair) :
    Procedure pairCode (listCode pairCode) (fun p => xs.map (qmaCellTranslate p)) :=
  (Procedure.listMapWith (0,0) (0,0) translateProgram).comp
    ((Procedure.identity pairCode).pair (Procedure.constant pairCode (listCode pairCode) xs))

noncomputable opaque neighborProgram (a : Fin 4) : Procedure pairCode pairCode
    (fun p => qmaGridNeighbor p a) := by
  let x := Procedure.first Nat.bits Nat.bits
  let y := Procedure.second Nat.bits Nat.bits
  let c := Procedure.constant pairCode Nat.bits 1
  by_cases h0 : a = 0
  · subst a
    exact ((Procedure.binaryAdd.comp (x.pair c)).pair y).congrFun (by intro p; rfl)
  by_cases h1 : a = 1
  · subst a
    exact (x.pair (Procedure.binaryAdd.comp (y.pair c))).congrFun (by intro p; rfl)
  by_cases h2 : a = 2
  · subst a
    exact ((Procedure.binarySub.comp (x.pair c)).pair y).congrFun (by intro p; rfl)
  have h3 : a = 3 := by omega
  subst a
  exact (x.pair (Procedure.binarySub.comp (y.pair c))).congrFun (by intro p; rfl)

noncomputable opaque rayProgram (a : Fin 4) : Procedure pairCode (listCode pairCode)
    (fun p => (QMACellRouteBody.ray p a).path) := translatedPathProgram (qmaCellRayPath a)

noncomputable opaque pairProgram (e : Fin 6) : Procedure pairCode (listCode pairCode)
    (fun p => (QMACellRouteBody.pair p e).path) := translatedPathProgram (qmaCellPairPath e)

noncomputable opaque patchProgram (e : Fin 9) : Procedure pairCode (listCode pairCode)
    (fun p => (QMACellRouteBody.patch p e).path) :=
  (translatedPathProgram (qmaLocalPatchPath e)).congrFun (by
    intro p
    simp only [qmaLocalPatchPath,List.map_map,Function.comp_def,QMACellRouteBody.path,
      qmaCrossingPathAt]
    congr 1
    funext z
    exact qmaCellTranslate_patch p z)

noncomputable opaque halfProgram (a : Fin 4) (b : Bool) : Procedure pairCode (listCode pairCode)
    (fun p => qmaHalfPathAt p b a) := translatedPathProgram (qmaHalfCorridorPath b a)

noncomputable opaque corridorProgram (a : Fin 4) (b c : Bool) :
    Procedure pairCode (listCode pairCode) (fun p => (QMACellRouteBody.corridor p a b c).path) := by
  let first := halfProgram a b
  let second := (Procedure.listReverse pairCode (0,0)).comp
    ((halfProgram (qmaPortOpposite a) c).comp (neighborProgram a))
  exact (Procedure.listAppend pairCode (0,0)).comp (first.pair second)

end ContinuumCoulomb.QuantumCellPathProgram

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

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem internal_bodies_disjoint
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (p q : ℕ × ℕ) (e f : QMAInternalEdge) (hne : p ≠ q ∨ e ≠ f)
    (he : P.RoutingAllowed (qmaInternalBody p e))
    (hf : P.RoutingAllowed (qmaInternalBody q f)) :
    Disjoint ((((qmaInternalBody p e).path).drop 1).dropLast).toFinset
      (qmaInternalBody q f).path.toFinset := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  have hz' := List.mem_toFinset.mp hz
  have hw' := List.mem_toFinset.mp hw
  rw [qmaInternalBody_path,← List.map_drop,← List.map_dropLast] at hz'
  rw [qmaInternalBody_path] at hw'
  obtain ⟨u,hu,heu⟩ := List.mem_map.mp hz'
  obtain ⟨v,hv,hev⟩ := List.mem_map.mp hw'
  have hu' := List.mem_of_mem_drop (List.mem_of_mem_dropLast hu)
  have hh := qmaCellTranslate_unique (qmaInternalPath_bounded e u hu')
    (qmaInternalPath_bounded f v hv) (heu.trans hev.symm)
  rcases hh with ⟨rfl,rfl⟩
  have hef : e ≠ f := hne.resolve_left (by intro h; exact h rfl)
  exact Finset.disjoint_left.mp (P.internal_allowed_disjoint havoid p e f hef he hf)
    (List.mem_toFinset.mpr hu) (List.mem_toFinset.mpr hv)

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumInternalHalfSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two orientations of the internal-path/external-corridor separation. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem internal_half_disjoint (p : ℕ × ℕ) (e : QMAInternalEdge) (a : Fin 4)
    (b : Bool) (he : P.RoutingAllowed (qmaInternalBody p e)) (hb : b = decide (P.IsCrossing p)) :
    Disjoint (((qmaInternalPath e).drop 1).dropLast).toFinset (qmaHalfCorridorPath b a).toFinset := by
  subst b
  rcases e with e | (e | e)
  · have hn : ¬P.IsCrossing p := he.2
    simpa only [qmaInternalPath,hn,decide_false] using qmaCellRay_half e a
  · have hn : ¬P.IsCrossing p := he.1
    simpa only [qmaInternalPath,hn,decide_false] using qmaCellPair_half e a
  · have hp : P.IsCrossing p := he
    simpa only [qmaInternalPath,hp,decide_true] using qmaLocalPatch_half e a

theorem internal_halfAt_disjoint (p q : ℕ × ℕ) (e : QMAInternalEdge) (a : Fin 4)
    (b : Bool) (he : P.RoutingAllowed (qmaInternalBody p e)) (hb : b = decide (P.IsCrossing q)) :
    Disjoint ((((qmaInternalBody p e).path).drop 1).dropLast).toFinset
      (qmaHalfPathAt q b a).toFinset := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  have hz' := List.mem_toFinset.mp hz
  rw [qmaInternalBody_path,← List.map_drop,← List.map_dropLast] at hz'
  obtain ⟨u,hu,heu⟩ := List.mem_map.mp hz'
  obtain ⟨v,hv,hev⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  have hu' := List.mem_of_mem_drop (List.mem_of_mem_dropLast hu)
  have hh := qmaCellTranslate_unique (qmaInternalPath_bounded e u hu')
    (qmaHalfCorridor_bounded b a v hv) (heu.trans hev.symm)
  rcases hh with ⟨rfl,rfl⟩
  exact Finset.disjoint_left.mp (P.internal_half_disjoint p e a b he hb)
    (List.mem_toFinset.mpr hu) (List.mem_toFinset.mpr hv)

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCorridorSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete corridor separation: internal paths only meet corridors at their
terminals, and different physical corridors have disjoint full paths. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem internal_corridor_disjoint (p q : ℕ × ℕ) (e : QMAInternalEdge) (a : Fin 4)
    (b c : Bool) (he : P.RoutingAllowed (qmaInternalBody p e))
    (hc : P.RoutingAllowed (.corridor q a b c)) :
    Disjoint ((((qmaInternalBody p e).path).drop 1).dropLast).toFinset
      (qmaCellCorridor q a b c).toFinset := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  obtain ⟨t,ht⟩ := qmaCellCorridor_mem_half (List.mem_toFinset.mp hw)
  exact Finset.disjoint_left.mp (P.internal_halfAt_disjoint p (qmaCorridorHalfCell q a t) e
    (qmaCorridorHalfPort a t) (qmaCorridorHalfMode b c t) he
    (qmaCorridorHalf_mode P.IsCrossing q a b c hc.1 hc.2 t)) hz (List.mem_toFinset.mpr ht)

end QMAPortRouteData
end ContinuumCoulomb

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

noncomputable def sumMapProgram {f : ℚ → ℚ} (p : Procedure ratCode ratCode f) :
    Procedure (listCode ratCode) ratCode (fun xs => (xs.map f).sum) :=
  RationalSumProgram.sumProgram.comp (Procedure.listMap 0 0 p)

end ContinuumCoulomb.QuantumPathScaleProgram

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
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque baseProgram : Procedure inputCode Nat.bits base := by
  let n := Procedure.unaryToBits.comp
    ((Procedure.first unaryCode ratCode).comp (Procedure.first parametersCode (prodCode unaryCode crossingCode)))
  let i := Procedure.unaryToBits.comp
    ((Procedure.first unaryCode crossingCode).comp (Procedure.second parametersCode (prodCode unaryCode crossingCode)))
  exact Procedure.binaryAdd.comp (n.pair
    (Procedure.binaryMul.comp ((Procedure.constant inputCode Nat.bits 2).pair i)))
noncomputable opaque nextProgram : Procedure inputCode Nat.bits (fun x => base x+1) :=
  Procedure.binaryAdd.comp (baseProgram.pair (Procedure.constant inputCode Nat.bits 1))
noncomputable opaque leftProgram (k : Fin 9) : Procedure inputCode Nat.bits (fun x => left x k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 0
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 0
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 1
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 2
  refine Fin.cases ?_ (fun k => ?_) k
  · exact baseProgram
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 0
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 1
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 2
  refine Fin.cases ?_ (fun k => Fin.elim0 k) k
  exact siteProgram 3

noncomputable opaque rightProgram (k : Fin 9) : Procedure inputCode Nat.bits (fun x => right x k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 1
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 3
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 2
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 3
  refine Fin.cases ?_ (fun k => ?_) k
  · exact nextProgram
  refine Fin.cases ?_ (fun k => ?_) k
  · exact baseProgram
  refine Fin.cases ?_ (fun k => ?_) k
  · exact baseProgram
  refine Fin.cases ?_ (fun k => ?_) k
  · exact nextProgram
  refine Fin.cases ?_ (fun k => Fin.elim0 k) k
  exact nextProgram

noncomputable opaque coefficientsProgram (k : Fin 10) :
    Procedure inputCode ratCode (fun x => QuantumRoutingCode.coefficients (x.1.2,x.2.2.1) k) :=
  (QuantumRoutingCode.coefficientProgram k).comp
    (radiusProgram.pair ((Procedure.first (prodCode ratCode ratCode) sitesCode).comp crossingProgram))
noncomputable opaque coefficientProgram (k : Fin 9) :
    Procedure inputCode ratCode (fun x => coefficient x k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact coefficientsProgram 5
  refine Fin.cases ?_ (fun k => ?_) k
  · exact coefficientsProgram 6
  refine Fin.cases ?_ (fun k => ?_) k
  · exact coefficientsProgram 7
  refine Fin.cases ?_ (fun k => ?_) k
  · exact coefficientsProgram 8
  refine Fin.cases ?_ (fun k => ?_) k
  · exact QuantumRoutingCode.squareProgram radiusProgram
  refine Fin.cases ?_ (fun k => ?_) k
  · exact coefficientsProgram 1
  refine Fin.cases ?_ (fun k => ?_) k
  · exact coefficientsProgram 2
  refine Fin.cases ?_ (fun k => ?_) k
  · exact coefficientsProgram 3
  refine Fin.cases ?_ (fun k => Fin.elim0 k) k
  exact coefficientsProgram 4

noncomputable opaque bondProgram (k : Fin 9) : Procedure inputCode bondCode (fun x => bond x k) :=
  (leftProgram k).pair ((rightProgram k).pair (coefficientProgram k))
noncomputable opaque blockProgram : Procedure inputCode (listCode bondCode) block :=
  QuantumRawExchange.fixedListProgram inputCode bondCode 9 (fun k x => bond x k) bondProgram

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
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque indexedProgram : Procedure (prodCode unaryCode familyCode) inputCode indexed := by
  let i := Procedure.first unaryCode familyCode
  let x := Procedure.second unaryCode familyCode
  let p := (Procedure.first parametersCode (listCode crossingCode)).comp x
  let cs := (Procedure.second parametersCode (listCode crossingCode)).comp x
  let c := (Procedure.listGet crossingCode zeroCrossing).comp ((Procedure.unaryToBits.comp i).pair cs)
  exact p.pair (i.pair c)
noncomputable opaque familyProgram : Procedure familyCode (listCode bondCode) family := by
  let n := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength crossingCode zeroCrossing).comp
    (Procedure.second parametersCode (listCode crossingCode))
  let tab := (Procedure.tabulate (f := fun x i => block (indexed (i,x))) []
    (blockProgram.comp indexedProgram)).comp (n.pair (Procedure.identity familyCode))
  exact (QuantumRawExchange.flattenProgram bondCode zeroBond).comp tab
noncomputable opaque offsetProgram : Procedure inputCode ratCode offset := coefficientsProgram 9
noncomputable opaque familyOffsetProgram : Procedure familyCode ratCode familyOffset := by
  let p := Procedure.first parametersCode crossingCode
  let c := Procedure.second parametersCode crossingCode
  let entry := offsetProgram.comp (p.pair ((Procedure.constant _ unaryCode 0).pair c))
  exact RationalSumProgram.sumProgram.comp
    (Procedure.listMapWith (ea := parametersCode) (eb := crossingCode) (ec := ratCode)
      (f := fun p c => offset (p,0,c)) zeroCrossing 0 entry)

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

noncomputable opaque linearProgram : Procedure pairCode ratCode linearCost :=
  Procedure.ratAdd.comp ((Procedure.ratAdd.comp
    ((Procedure.constant pairCode ratCode 1).pair
      (MediatorProgram.absoluteProgram.comp (Procedure.first ratCode ratCode)))).pair
    (MediatorProgram.absoluteProgram.comp (Procedure.second ratCode ratCode)))
noncomputable opaque squareProgram : Procedure pairCode ratCode squareCost :=
  QuantumRoutingCode.squareProgram linearProgram
noncomputable def sumMapProgram {f : Pair → ℚ} (p : Procedure pairCode ratCode f) :
    Procedure (listCode pairCode) ratCode (fun xs => (xs.map f).sum) :=
  RationalSumProgram.sumProgram.comp (Procedure.listMap (0,0) 0 p)
noncomputable opaque program : Procedure inputCode ratCode value := by
  let params := Procedure.first pairCode (prodCode (listCode ratCode) (listCode pairCode))
  let lists := Procedure.second pairCode (prodCode (listCode ratCode) (listCode pairCode))
  let n := (Procedure.first ratCode ratCode).comp params
  let c := (Procedure.second ratCode ratCode).comp params
  let retained := (Procedure.first (listCode ratCode) (listCode pairCode)).comp lists
  let selected := (Procedure.second (listCode ratCode) (listCode pairCode)).comp lists
  let b := Procedure.ratAdd.comp
    ((Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 3).pair
      ((QuantumPathScaleProgram.sumMapProgram MediatorProgram.absoluteProgram).comp retained))).pair
      (MediatorProgram.absoluteProgram.comp c))
  let a := Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 6).pair
    ((sumMapProgram linearProgram).comp selected))
  let d := Procedure.ratAdd.comp (b.pair
    (Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 12).pair
      ((sumMapProgram squareProgram).comp selected))))
  exact QuantumRoutingCode.scaleProgram.comp (a.pair (d.pair n))

def actualInput {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) : Input :=
  ((N,C.base.constant),(List.ofFn (fun i => C.base.weight (labels.symm i)),
    List.ofFn (fun i => (C.J i,C.K i))))

end ContinuumCoulomb.QuantumCrossingScaleProgram

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

def outputCode : Output → List Bool := prodCode unaryCode (prodCode (listCode bondCode) ratCode)

noncomputable opaque weightProgram : Procedure bondCode ratCode (fun e => e.2.2) :=
  (Procedure.second _ _).comp (Procedure.second _ _)
noncomputable opaque weightsProgram : Procedure (listCode bondCode) (listCode ratCode)
    (fun xs => xs.map (fun e => e.2.2)) := Procedure.listMap zeroBond 0 weightProgram

end ContinuumCoulomb.QuantumListPathStep

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingListLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete rational crossing transformation, including its calibrated
scale, retained edges, mediator pairs and exact scalar shift. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListLayer
open ExactQuantumFactoring.BitStackProgram MediatorListProgram
open QuantumCrossingListBlock

abbrev Input := (ℚ × QuantumListPathStep.Output) × List Crossing
def inputCode : Input → List Bool :=
  prodCode (prodCode ratCode QuantumListPathStep.outputCode) (listCode crossingCode)

def scaleInput (x : Input) : QuantumCrossingScaleProgram.Input :=
  ((x.1.1,x.1.2.2.2),(x.1.2.2.1.map (fun b => b.2.2),x.2.map Prod.fst))
def parameters (x : Input) : Parameters := (x.1.2.1,QuantumCrossingScaleProgram.value (scaleInput x))
def familyInput (x : Input) : FamilyInput := (parameters x,x.2)
def count (x : Input) : ℕ := x.1.2.1+2*x.2.length
def bonds (x : Input) : List Bond := x.1.2.2.1++family (familyInput x)
def constant (x : Input) : ℚ := x.1.2.2.2+familyOffset (familyInput x)
def value (x : Input) : QuantumListPathStep.Output := (count x,bonds x,constant x)

noncomputable opaque packetProgram : Procedure inputCode QuantumListPathStep.outputCode
    (fun x => x.1.2) :=
  (Procedure.second ratCode QuantumListPathStep.outputCode).comp
    (Procedure.first (prodCode ratCode QuantumListPathStep.outputCode) (listCode crossingCode))
noncomputable opaque nProgram : Procedure inputCode unaryCode (fun x => x.1.2.1) :=
  (Procedure.first unaryCode (prodCode (listCode bondCode) ratCode)).comp packetProgram
noncomputable opaque oldProgram : Procedure inputCode (prodCode (listCode bondCode) ratCode)
    (fun x => x.1.2.2) :=
  (Procedure.second unaryCode (prodCode (listCode bondCode) ratCode)).comp packetProgram
noncomputable opaque oldBondsProgram : Procedure inputCode (listCode bondCode)
    (fun x => x.1.2.2.1) :=
  (Procedure.first (listCode bondCode) ratCode).comp oldProgram
noncomputable opaque oldConstantProgram : Procedure inputCode ratCode
    (fun x => x.1.2.2.2) :=
  (Procedure.second (listCode bondCode) ratCode).comp oldProgram
noncomputable opaque crossingProgram : Procedure inputCode (listCode crossingCode) Prod.snd :=
  Procedure.second (prodCode ratCode QuantumListPathStep.outputCode) (listCode crossingCode)
noncomputable opaque scaleInputProgram :
    Procedure inputCode QuantumCrossingScaleProgram.inputCode scaleInput := by
  let N := (Procedure.first ratCode QuantumListPathStep.outputCode).comp
    (Procedure.first (prodCode ratCode QuantumListPathStep.outputCode) (listCode crossingCode))
  let pairs := (Procedure.listMap zeroCrossing (0,0)
    (Procedure.first (prodCode ratCode ratCode) sitesCode)).comp crossingProgram
  exact (N.pair oldConstantProgram).pair
    (((QuantumListPathStep.weightsProgram).comp oldBondsProgram).pair pairs)
noncomputable opaque parametersProgram : Procedure inputCode parametersCode parameters :=
  nProgram.pair (QuantumCrossingScaleProgram.program.comp scaleInputProgram)
noncomputable opaque familyInputProgram : Procedure inputCode familyCode familyInput :=
  parametersProgram.pair crossingProgram
noncomputable opaque countProgram : Procedure inputCode unaryCode count := by
  let r := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength crossingCode zeroCrossing).comp crossingProgram
  exact Procedure.unaryAdd.comp (nProgram.pair
    (Procedure.unaryMul.comp ((Procedure.constant inputCode unaryCode 2).pair r)))
noncomputable opaque bondsProgram : Procedure inputCode (listCode bondCode) bonds :=
  (Procedure.listAppend bondCode zeroBond).comp
    (oldBondsProgram.pair (QuantumCrossingListBlock.familyProgram.comp familyInputProgram))
noncomputable opaque constantProgram : Procedure inputCode ratCode constant :=
  Procedure.ratAdd.comp (oldConstantProgram.pair
    (QuantumCrossingListBlock.familyOffsetProgram.comp familyInputProgram))
noncomputable opaque program : Procedure inputCode QuantumListPathStep.outputCode value :=
  countProgram.pair (bondsProgram.pair constantProgram)

theorem bonds_bounded (x : Input)
    (hb : SourceBondLists.bounded x.1.2.1 x.1.2.2.1)
    (hs : ∀ c ∈ x.2, ∀ a, site c.2 a < x.1.2.1) :
    SourceBondLists.bounded (count x) (bonds x) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact ⟨(hb e he).1.trans_le (Nat.le_add_right _ _),
      (hb e he).2.trans_le (Nat.le_add_right _ _)⟩
  · exact family_bounded (familyInput x) hs e he

theorem bonds_noLoops (x : Input)
    (hn : ∀ e ∈ x.1.2.2.1, e.1 ≠ e.2.1)
    (hs : ∀ c ∈ x.2, ∀ a, site c.2 a < x.1.2.1)
    (hinj : ∀ c ∈ x.2, Function.Injective (site c.2)) :
    ∀ e ∈ bonds x, e.1 ≠ e.2.1 := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hn e he
  · exact family_noLoops (familyInput x) hs hinj e he

def graph (x : Input) (hb : SourceBondLists.bounded x.1.2.1 x.1.2.2.1)
    (hn : ∀ e ∈ x.1.2.2.1, e.1 ≠ e.2.1)
    (hs : ∀ c ∈ x.2, ∀ a, site c.2 a < x.1.2.1)
    (hinj : ∀ c ∈ x.2, Function.Injective (site c.2)) : QMARationalExchangeGraph :=
  QuantumListGraph.ofBonds (count x) (bonds x) (constant x)
    (bonds_bounded x hb hs) (bonds_noLoops x hn hs hinj)

end ContinuumCoulomb.QuantumCrossingListLayer

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingListActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal crossing packet has exactly the sites, scale and scalar
shift of the rational crossing layer used by the spectral comparison. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListLayer
open QuantumCrossingListBlock
open scoped BigOperators Classical

def actualCrossing {r : ℕ} (C : QMARationalCrossingLayer r) (i : Fin r) : Crossing :=
  ((C.J i,C.K i),((C.site i 0).val,(C.site i 1).val),
    ((C.site i 2).val,(C.site i 3).val))
def actualInput {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) : Input :=
  ((N,C.base.n,QuantumListGraph.packed C.base labels,C.base.constant),
    List.ofFn (actualCrossing C))

theorem site_actual {r : ℕ} (C : QMARationalCrossingLayer r) (i : Fin r) (a : Fin 4) :
    site (actualCrossing C i).2 a=(C.site i a).val := by
  fin_cases a <;> rfl

theorem count_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    count (actualInput C N labels)=(C.output N).n := by
  simp only [count,actualInput,List.length_ofFn,QMARationalCrossingLayer.output]
  omega

theorem sites_bounded {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    ∀ c ∈ (actualInput C N labels).2, ∀ a, site c.2 a < (actualInput C N labels).1.2.1 := by
  intro c hc a
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
  rw [site_actual]
  exact (C.site i a).isLt

theorem sites_injective {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    ∀ c ∈ (actualInput C N labels).2, Function.Injective (site c.2) := by
  intro c hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
  intro a b hab
  rw [site_actual,site_actual] at hab
  exact C.injective i (Fin.ext hab)

def actualGraph {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) : QMARationalExchangeGraph :=
  graph (actualInput C N labels) (QuantumListGraph.packed_bounded C.base labels)
    (QuantumListGraph.packed_noLoops C.base labels)
    (sites_bounded C N labels) (sites_injective C N labels)

end ContinuumCoulomb.QuantumCrossingListLayer

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingListMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full-space matrix semantics for the computed crossing packet.
The nine serialized bonds are the nine physical edges of each crossing. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListLayer
open QuantumCrossingListBlock MediatorGraph
open scoped BigOperators Classical

def edgeTag {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ)
    (i : Fin r) : Fin 9 → (C.output N).Edge :=
  ![.inl (.inr (i,0)),.inl (.inr (i,1)),.inl (.inr (i,2)),.inl (.inr (i,3)),
    .inr (.inl i),.inr (.inr (i,0)),.inr (.inr (i,1)),
    .inr (.inr (i,2)),.inr (.inr (i,3))]

end ContinuumCoulomb.QuantumCrossingListLayer

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSelectProgram
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

noncomputable opaque hitsProgram : Procedure (prodCode bondCode pairCode) Procedure.boolCode hits := by
  let e := Procedure.first bondCode pairCode
  let p := Procedure.second bondCode pairCode
  let l := (Procedure.first Nat.bits (prodCode Nat.bits ratCode)).comp e
  let r := (Procedure.first Nat.bits ratCode).comp
    ((Procedure.second Nat.bits (prodCode Nat.bits ratCode)).comp e)
  exact Procedure.boolOr.comp
    ((QuantumFiniteMembership.pairEqProgram.comp ((l.pair r).pair p)).pair
      (QuantumFiniteMembership.pairEqProgram.comp ((r.pair l).pair p)))

noncomputable opaque contributionProgram :
    Procedure (prodCode bondCode pairCode) ratCode contribution := by
  let e := Procedure.first bondCode pairCode
  let w := (Procedure.second Nat.bits ratCode).comp
    ((Procedure.second Nat.bits (prodCode Nat.bits ratCode)).comp e)
  exact Procedure.conditional hitsProgram w (Procedure.constant _ ratCode 0)

abbrev Input := ℚ × (QuantumListPathStep.Output × List Sites)
def inputCode : Input → List Bool :=
  prodCode ratCode (prodCode QuantumListPathStep.outputCode (listCode sitesCode))
def value (x : Input) : QuantumCrossingListLayer.Input :=
  ((x.1,x.2.1.1,retained (pairs x.2.2,x.2.1.2.1),x.2.1.2.2),
    crossings (x.2.1.2.1,x.2.2))

noncomputable opaque precisionProgram : Procedure inputCode ratCode Prod.fst := Procedure.first _ _
noncomputable opaque packetProgram :
    Procedure inputCode QuantumListPathStep.outputCode (fun x => x.2.1) :=
  (Procedure.first QuantumListPathStep.outputCode (listCode sitesCode)).comp
    (Procedure.second ratCode (prodCode QuantumListPathStep.outputCode (listCode sitesCode)))
noncomputable opaque bondsProgram : Procedure inputCode (listCode bondCode) (fun x => x.2.1.2.1) :=
  (Procedure.first (listCode bondCode) ratCode).comp
    ((Procedure.second unaryCode (prodCode (listCode bondCode) ratCode)).comp packetProgram)

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingCompiled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space correctness of the computed crossing transformation, starting
from an ordinary finite bond tape and its selected physical terminals. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open QuantumCrossingListBlock
open scoped Classical

variable {G : QMARationalExchangeGraph} {r : ℕ}
    (S : QMARationalCrossingSelection G r) {m : ℕ} (labels : G.Edge ≃ Fin m)

def retainedGraph : QMARationalExchangeGraph :=
  QuantumListGraph.ofBonds G.n
    (retained (pairs (List.ofFn (encodedSites S.site)),QuantumListGraph.packed G labels))
    G.constant
    (retained_bounded _ _ (QuantumListGraph.packed_bounded G labels))
    (retained_noLoops _ _ (QuantumListGraph.packed_noLoops G labels))

def computedLayer : QMARationalCrossingLayer r where
  base := retainedGraph S labels
  site := S.site
  injective := S.injective
  J i := weight (QuantumListGraph.packed G labels,terminalPair 0 (encodedSites S.site i))
  K i := weight (QuantumListGraph.packed G labels,terminalPair 1 (encodedSites S.site i))

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingListSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal nine-bond crossing block has precisely the unordered
endpoint support of the physical crossing graph. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListLayer
open QuantumCrossingListBlock
open scoped Classical

variable {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ)

def actualVertex {m : ℕ} (labels : C.base.Edge ≃ Fin m) :
    Fin (actualGraph C N labels).n ≃ Fin (C.output N).n :=
  finCongr (count_actual C N labels)

end ContinuumCoulomb.QuantumCrossingListLayer

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingPacketEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space crossing error stated directly for the serialized bond packet. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingPacketEnergy
open QuantumCrossingListBlock MediatorListProgram QuantumCrossingSelectProgram
open scoped Classical

def energy (x : QuantumListPathStep.Output) : ℝ :=
  sourceMatrixBottom x.1 (SourceBondLists.matrix x.1 x.2.1+(x.2.2:ℂ) • 1)

end ContinuumCoulomb.QuantumCrossingPacketEnergy

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortChainProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

noncomputable def offsetProgram (x y : ℕ) : Procedure pairCode pairCode
    (fun p => offset p x y) := by
  let coord (p : Procedure pairCode Nat.bits Prod.fst) (c : ℕ) :=
    Procedure.binaryAdd.comp
      ((Procedure.binaryMul.comp ((Procedure.constant pairCode Nat.bits 32).pair p)).pair
        (Procedure.constant pairCode Nat.bits c))
  let py := Procedure.second Nat.bits Nat.bits
  let vy := Procedure.binaryAdd.comp
    ((Procedure.binaryMul.comp ((Procedure.constant pairCode Nat.bits 32).pair py)).pair
      (Procedure.constant pairCode Nat.bits y))
  exact (coord (Procedure.first Nat.bits Nat.bits) x).pair vy

noncomputable def centerProgram : Procedure pairCode pairCode qmaExpandedPoint :=
  offsetProgram 16 16

def point (xs : List Pair) (k : ℕ) : Pair :=
  qmaPortChain (QuantumPathVisitProgram.lookup xs) (xs.length-1) k

def value (xs : List Pair) : List Pair :=
  (List.range (2*(xs.length-1)+2)).map (point xs)

@[simp] theorem value_length (xs : List Pair) : (value xs).length = 2*(xs.length-1)+2 := by
  simp only [value,List.length_map,List.length_range]

end ContinuumCoulomb.QuantumPortChainProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingPositionProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.qmaPointCell_ancilla _root_.OAI.ContinuumCoulomb.qmaPointCell_inner _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal physical coordinates after crossing removal. Only ports in the
computed crossing cells move; the two fresh spins use fixed local coordinates. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingPositionProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode
open scoped Classical

abbrev Input := List Pair × Pair
def inputCode : Input → List Bool := prodCode (listCode pairCode) pairCode
def cell (z : Pair) : Pair := (z.1/32,z.2/32)
def move (x : Input) : Pair := qmaCrossingMove (fun p => p ∈ x.1) x.2

noncomputable opaque cellProgram : Procedure pairCode pairCode cell := by
  let c := Procedure.constant pairCode Nat.bits 32
  exact (Procedure.binaryDiv.comp ((Procedure.first Nat.bits Nat.bits).pair c)).pair
    (Procedure.binaryDiv.comp ((Procedure.second Nat.bits Nat.bits).pair c))

noncomputable opaque innerProgram (a : Fin 4) : Procedure pairCode pairCode
    (fun p => qmaInnerPort p a) := by
  refine ((QuantumCellPathProgram.translateProgram).comp
    ((Procedure.identity pairCode).pair
      (Procedure.constant pairCode pairCode (qmaInnerPort (0,0) a)))).congrFun ?_
  intro p
  fin_cases a <;> simp [qmaCellTranslate,qmaInnerPort]

noncomputable opaque ancillaProgram (a : Fin 2) : Procedure pairCode pairCode
    (fun p => qmaGadgetAncilla p a) := by
  refine ((QuantumCellPathProgram.translateProgram).comp
    ((Procedure.identity pairCode).pair
      (Procedure.constant pairCode pairCode (qmaGadgetAncilla (0,0) a)))).congrFun ?_
  intro p
  fin_cases a <;> simp [qmaCellTranslate,qmaGadgetAncilla]

noncomputable opaque chosenInnerProgram : Procedure pairCode pairCode
    (fun z => qmaInnerPort (cell z) (qmaPortIndex z)) := by
  let c := Procedure.constant pairCode Nat.bits 32
  let rx := Procedure.binaryMod.comp ((Procedure.first Nat.bits Nat.bits).pair c)
  let ry := Procedure.binaryMod.comp ((Procedure.second Nat.bits Nat.bits).pair c)
  let eq (p : Procedure pairCode Nat.bits (fun z => z.1%32)) (n : ℕ) :=
    Procedure.binaryEq.comp (p.pair (Procedure.constant pairCode Nat.bits n))
  let x23 := eq rx 23
  let y23 := Procedure.binaryEq.comp (ry.pair (Procedure.constant pairCode Nat.bits 23))
  let x9 := eq rx 9
  exact (Procedure.conditional x23 ((innerProgram 0).comp cellProgram)
    (Procedure.conditional y23 ((innerProgram 1).comp cellProgram)
      (Procedure.conditional x9 ((innerProgram 2).comp cellProgram)
        ((innerProgram 3).comp cellProgram)))).congrFun (by
      intro z
      simp only [Function.comp_apply,qmaPortIndex,decide_eq_true_eq]
      split_ifs <;> rfl)

noncomputable opaque moveProgram : Procedure inputCode pairCode move := by
  let cs := Procedure.first (listCode pairCode) pairCode
  let z := Procedure.second (listCode pairCode) pairCode
  let p := cellProgram.comp z
  let memp := QuantumFiniteMembership.pairMemberProgram.comp (p.pair cs)
  let center := QuantumPortChainProgram.centerProgram.comp p
  let isCenter := QuantumFiniteMembership.pairEqProgram.comp (z.pair center)
  exact (Procedure.conditional
    (Procedure.boolAnd.comp (memp.pair (Procedure.boolNot.comp isCenter)))
    (chosenInnerProgram.comp z) z).congrFun (by
      intro x
      simp only [Function.comp_apply,move,qmaCrossingMove,cell,Bool.and_eq_true,decide_eq_true_eq,
        Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not])

def moved (x : List Pair × List Pair) : List Pair := x.2.map (fun z => move (x.1,z))
def fresh (cs : List Pair) : List Pair :=
  (cs.map (fun p => [qmaGadgetAncilla p 0,qmaGadgetAncilla p 1])).flatten
def positions (x : List Pair × List Pair) : List Pair := moved x++fresh x.1

noncomputable opaque movedProgram :
    Procedure (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode) moved :=
  Procedure.listMapWith (f := fun cs z => move (cs,z)) (0,0) (0,0) moveProgram

noncomputable opaque freshProgram : Procedure (listCode pairCode) (listCode pairCode) fresh := by
  let pair := (Procedure.listCons pairCode).comp ((ancillaProgram 0).pair
    ((Procedure.listCons pairCode).comp ((ancillaProgram 1).pair
      (Procedure.constant pairCode (listCode pairCode) []))))
  exact (QuantumRawExchange.flattenProgram pairCode (0,0)).comp
    (Procedure.listMap (0,0) [] pair)

noncomputable opaque positionsProgram :
    Procedure (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode) positions :=
  (Procedure.listAppend pairCode (0,0)).comp (movedProgram.pair
    (freshProgram.comp (Procedure.first (listCode pairCode) (listCode pairCode))))

end ContinuumCoulomb.QuantumCrossingPositionProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingPositionRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reordering the port vertices or crossing cells reorders the output
positions by a finite equivalence, preserving their injectivity. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingPositionProgram
open MediatorGraph QuantumRouteCode
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) (D : ℕ) {n r : ℕ}
    (σ : Fin n ≃ Fin (P.finishedGraph N D).n)
    (τ : Fin r ≃ Fin P.crossingCells.card)

def extend : Fin (n+r*2) ≃ Fin ((P.finishedGraph N D).n+P.crossingCells.card*2) :=
  ((vertexEquiv n r).symm.trans (Equiv.sumCongr σ
    (Equiv.prodCongr τ (Equiv.refl (Fin 2))))).trans (vertexEquiv _ _)

end ContinuumCoulomb.QuantumCrossingPositionProgram

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

abbrev Input := List Pair × Pair
def flags (x : Input) : List Bool := x.1.map (fun p => decide (p=x.2))

end ContinuumCoulomb.QuantumCrossingSiteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSupportRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A crossing layer preserves unordered edge support under relabeling of
the old vertices and crossing cells. Couplings do not enter this statement. -/

noncomputable section
namespace ContinuumCoulomb.QMARationalCrossingLayer
open MediatorGraph
open scoped Classical

variable {r s : ℕ} (C : QMARationalCrossingLayer r) (E : QMARationalCrossingLayer s)
    (vertex : Fin C.base.n ≃ Fin E.base.n) (cell : Fin r ≃ Fin s)

def vertexRelabel : Fin (C.base.n+r*2) ≃ Fin (E.base.n+s*2) :=
  ((vertexEquiv C.base.n r).symm.trans
    (Equiv.sumCongr vertex (Equiv.prodCongr cell (Equiv.refl (Fin 2))))).trans
      (vertexEquiv E.base.n s)

end ContinuumCoulomb.QMARationalCrossingLayer

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumMergeEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Parallel interactions are combined at one canonically ordered physical edge.
This is an exact matrix operation, with no perturbative error. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
namespace QMARationalExchangeGraph

theorem merge_pair_injective (G : QMARationalExchangeGraph) :
    Function.Injective (fun e : G.merge.Edge => (G.merge.left e,G.merge.right e)) := by
  intro e f h
  exact Subtype.ext h

end QMARationalExchangeGraph
end ContinuumCoulomb

end

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

namespace QMARationalExchangeGraph
variable (G : QMARationalExchangeGraph)

theorem merge_simple : G.merge.Simple := by
  intro e f hef
  constructor
  · rintro ⟨hl,hr⟩
    exact hef (G.merge_pair_injective (Prod.ext hl hr))
  · rintro ⟨hl,hr⟩
    have he : G.merge.left e < G.merge.right e := G.mergedEdge_lt e
    have hf : G.merge.left f < G.merge.right f := G.mergedEdge_lt f
    rw [hl,hr] at he
    exact (not_lt_of_ge hf.le) he

end QMARationalExchangeGraph
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

theorem qmaMergedEndpointPairs_injective (G : QMARationalExchangeGraph)
    (position : Fin G.n → ℕ × ℕ) (hp : Function.Injective position) :
    Function.Injective (fun e : G.merge.Edge => s(position (G.merge.left e),position (G.merge.right e))) := by
  intro e f h
  rcases Sym2.eq_iff.mp h with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · exact G.merge_pair_injective (Prod.ext (hp hl) (hp hr))
  · have hleft := hp hl
    have hright := hp hr
    have he := G.mergedEdge_lt e
    have hf := G.mergedEdge_lt f
    change G.merge.left e < G.merge.right e at he
    change G.merge.left f < G.merge.right f at hf
    rw [hleft,hright] at he
    exact (lt_asymm he hf).elim

end ContinuumCoulomb

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

namespace QMARationalExchangeGraph

theorem orderedPair_endpointPair (G : QMARationalExchangeGraph) (e : G.Edge) :
    s((G.orderedPair e).1,(G.orderedPair e).2) = s(G.left e,G.right e) := by
  rcases le_total (G.left e) (G.right e) with h | h
  · simp only [orderedPair,min_eq_left h,max_eq_right h]
  · simpa only [orderedPair,min_eq_right h,max_eq_left h] using
      (Sym2.eq_swap : s(G.right e,G.left e) = s(G.left e,G.right e))

theorem merge_unordered_source (G : QMARationalExchangeGraph) (e : G.merge.Edge) :
    ∃ f : G.Edge, s(G.merge.left e,G.merge.right e) = s(G.left f,G.right f) := by
  obtain ⟨f,hf⟩ := G.merge_edge_source e
  exact ⟨f,Sym2.eq_iff.mpr hf⟩

theorem merge_unordered_target (G : QMARationalExchangeGraph) (f : G.Edge) :
    ∃ e : G.merge.Edge, s(G.merge.left e,G.merge.right e) = s(G.left f,G.right f) :=
  ⟨G.edgeClass f,G.orderedPair_endpointPair f⟩

end QMARationalExchangeGraph

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumNearestProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal nearest-neighbor gate compilation. All finite loops use the
unary work bound; malformed gate indices take the original singleton branch. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram

noncomputable def nearestProgram : Procedure nearestInputCode (listCode gateCode) nearestValue := by
  let work := Procedure.first unaryCode gateCode
  let gate := Procedure.second unaryCode gateCode
  let one := (Procedure.listCons gateCode).comp
    (gate.pair (Procedure.constant nearestInputCode (listCode gateCode) []))
  let dForward := Procedure.binarySub.comp
    ((Procedure.binarySub.comp (rightBits.pair leftBits)).pair
      (Procedure.constant nearestInputCode Nat.bits 1))
  let dBackward := Procedure.binarySub.comp
    ((Procedure.binarySub.comp (leftBits.pair rightBits)).pair
      (Procedure.constant nearestInputCode Nat.bits 1))
  let forward := adjacentProgram.comp ((Procedure.clippedUnary.comp (work.pair dForward)).pair
    (leftBits.pair (Procedure.constant nearestInputCode Procedure.boolCode true)))
  let backward := adjacentProgram.comp ((Procedure.clippedUnary.comp (work.pair dBackward)).pair
    (rightBits.pair (Procedure.constant nearestInputCode Procedure.boolCode false)))
  let cnot := Procedure.binaryEq.comp ((gateTagProgram.comp gate).pair
    (Procedure.constant nearestInputCode Nat.bits 2))
  exact (Procedure.conditional cnot
    (Procedure.conditional forwardGuardProgram forward
      (Procedure.conditional backwardGuardProgram backward one)) one).congrFun (by
        intro x
        simp only [nearestValue,Function.comp_apply,decide_eq_true_eq])

noncomputable def nearestListProgram :
    Procedure circuitCode (listCode gateCode) (fun c => c.gates.flatMap (qmaNearestGate c.work)) := by
  let rows := Procedure.listMapWith (ea := unaryCode) (eb := gateCode) (ec := listCode gateCode)
    (f := fun work g => nearestValue (work,g)) (.hadamard 0) [] nearestProgram
  exact ((QuantumRawExchange.flattenProgram gateCode (.hadamard 0)).comp
    (rows.comp (workProgram.pair gatesProgram))).congrFun (by
      intro c
      simp only [Function.comp_apply,List.flatMap_def]
      congr 1
      apply List.map_congr_left
      intro g _
      exact nearestValue_eq (c.work,g))

noncomputable def nearestCircuitProgram : Procedure circuitCode circuitCode qmaNearestCircuit :=
  (workProgram.pair (witnessProgram.pair nearestListProgram)).result (by intro c; rfl)

end ContinuumCoulomb.QuantumCircuitCode

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

def distributed (c : QMACircuit) (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    QMACircuitTerm c → Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) Scalar
  | .inl i => diagonal (fun s =>
      if s (Sum.inl i.castSucc) = 0 ∧ s (Sum.inl i.succ) = 1 then 1 else 0)
  | .inr (.inl b) => if b = 0 then
      diagonal (fun s => if s (Sum.inl 0) = 1 then 0 else 1) else
      diagonal (fun s => if s (Sum.inl (Fin.last (c.gates.length+1))) = 0 then 0 else 1)
  | .inr (.inr (.inl i)) => diagonal (fun s =>
      if qmaClockAt c.gates.length (τ i) (s ∘ Sum.inl) ∧
        qmaInputCheck c i (s ∘ Sum.inr) then 14 else 0)
  | .inr (.inr (.inr (.inl _))) => diagonal (fun s =>
      if s (Sum.inl (qmaOutputMarker c)) = 1 ∧ s (Sum.inr (Fin.last c.work)) ≠ 1 then 1 else 0)
  | .inr (.inr (.inr (.inr t))) => fun s r =>
      mul (rat ((14*(c.work+1)+8)*c.gates.length:ℚ))
        (lift (qmaPropagationSites c t) (propagationCore c t) s r)

def orderedTerm (c : QMACircuit) (hT : 0 < c.gates.length) :
    QMAReferenceTerm (qmaHistoryReferenceWork c) →
      Matrix (Fin (qmaHistoryReferenceWork c+1) ⊕ QMACircuitQubit c → Fin 2)
        (Fin (qmaHistoryReferenceWork c+1) ⊕ QMACircuitQubit c → Fin 2) Scalar
  | .inl i => rebit (qmaHistoryReferenceWork c+1) i
      (distributed c (qmaFirstUseTime c) (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i))
  | .inr i => referenceEdge (qmaHistoryReferenceWork c) i

def orderedCore (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    Matrix (QMASupportBasis ((qmaOrderedHistoryModel c hT).sites a))
      (QMASupportBasis ((qmaOrderedHistoryModel c hT).sites a)) Scalar :=
  fun s t => orderedTerm c hT a (qmaSupportExtend _ s) (qmaSupportExtend _ t)

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSupport
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem gateSites_finset (work : ℕ) (g : QMAGate) :
    (gateSites work g).toFinset = qmaGateSites work g := by
  cases g <;> simp [gateSites,qmaGateSites]

theorem propagationSites_finset (c : QMACircuit) (t : Fin c.gates.length) :
    (propagationSites c t).toFinset = qmaPropagationSites c t := by
  ext i
  simp [propagationSites,qmaPropagationSites,← gateSites_finset,Finset.mem_map]

theorem distributedSites_finset (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (a : QMACircuitTerm c) :
    (distributedSites c τ a).toFinset = qmaDistributedTermSites c τ a := by
  rcases a with i | (b | (i | (u | t)))
  · simp [distributedSites,qmaDistributedTermSites,qmaCircuitTermSites]
  · by_cases hb : b = 0 <;>
      simp [distributedSites,qmaDistributedTermSites,qmaCircuitTermSites,hb]
  · simp [distributedSites,qmaDistributedTermSites,qmaDistributedInputSites]
  · simp [distributedSites,qmaDistributedTermSites,qmaCircuitTermSites]
  · exact propagationSites_finset c t

def rawSites (c : QMACircuit) (hT : 0 < c.gates.length) :
    QMAReferenceTerm (qmaHistoryReferenceWork c) → List (Qubit c)
  | .inl i => Sum.inl i ::
      (distributedSites c (qmaFirstUseTime c)
        (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).map Sum.inr
  | .inr i => [Sum.inl i.castSucc,Sum.inl i.succ]

theorem rawSites_finset (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    (rawSites c hT a).toFinset = (qmaOrderedHistoryModel c hT).sites a := by
  cases a with
  | inl i =>
    ext x
    simp [rawSites,qmaOrderedHistoryModel,qmaReferenceTermSites,qmaDistributedRebitSites,
      qmaOrderedHistorySites,← distributedSites_finset,Finset.mem_map]
  | inr i => simp [rawSites,qmaOrderedHistoryModel,qmaReferenceTermSites,qmaReferenceEdgeSites]

def sites (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) : List (Qubit c) :=
  (rawSites c hT a).dedup

theorem sites_nodup (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) : (sites c hT a).Nodup := by
  exact List.nodup_dedup _

theorem sites_finset (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    (sites c hT a).toFinset = (qmaOrderedHistoryModel c hT).sites a := by
  rw [← rawSites_finset c hT a]; ext x; simp [sites]

def supportEquiv (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    Fin (sites c hT a).length ≃ {x // x ∈ (qmaOrderedHistoryModel c hT).sites a} :=
  (List.Nodup.getEquiv (sites c hT a) (sites_nodup c hT a)).trans
    (Equiv.subtypeEquivRight (fun x => by
      have he := congrArg (fun S : Finset (Qubit c) => x ∈ S) (sites_finset c hT a)
      exact List.mem_toFinset.symm.trans (Iff.of_eq he)))

end ContinuumCoulomb.QuantumOrderedSupport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal support-list order indexes the small matrix table.  Its
Pauli coefficients agree with the actual ordered-history coefficients. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

def orderedTable (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    Matrix (Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2)
      (Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) Scalar :=
  let e := QuantumOrderedSupport.supportEquiv c hT a
  fun s t => orderedCore c hT a (fun i => s (e.symm i)) (fun i => t (e.symm i))

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathVisitCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The encoded consecutive-point rule recovers the actual directional ports
of every interior visit in the proved port-route geometry. -/

noncomputable section
namespace ContinuumCoulomb
open QuantumRouteCode QuantumRoutingTable QuantumPathVisitProgram

namespace QuantumPathVisitProgram
 theorem lookup_range (f : ℕ → Pair) (n i : ℕ) (hi : i < n) :
    lookup ((List.range n).map f) i = f i := by
  simp only [lookup,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_map,
    List.getElem?_range hi,Option.map_some,Option.getD_some]

end QuantumPathVisitProgram

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

 theorem routeList_lookup (e : G.Edge) (i : ℕ) (hi : i ≤ P.length e) :
    lookup (P.routeList e) i = P.point e i :=
  QuantumPathVisitProgram.lookup_range _ _ _ (by omega)

 theorem routeList_visit (e : G.Edge) (j : Fin (P.length e-1)) :
    visit (P.routeList e) j.val =
      (P.cell ⟨e,j⟩,((P.port ⟨e,j⟩ 0).val,(P.port ⟨e,j⟩ 1).val)) := by
  have hj := j.isLt
  simp only [visit,P.routeList_lookup e j.val (by omega),
    P.routeList_lookup e (j.val+1) (by omega),P.routeList_lookup e (j.val+2) (by omega),
    cell,port,arm,armIndex,Fin.val_zero,Fin.val_one,mul_zero,mul_one,Nat.add_zero]

 theorem routeList_visits_general (e : G.Edge) (v : Visit) :
    v ∈ visits (P.routeList e) ↔
      ∃ j : Fin (P.length e-1),
        v ∈ both (P.cell ⟨e,j⟩,((P.port ⟨e,j⟩ 0).val,(P.port ⟨e,j⟩ 1).val)) := by
  have hlen : (P.routeList e).length-2 = P.length e-1 := by
    simp only [routeList,List.length_map,List.length_range]
    omega
  rw [visits,← List.flatMap_def,hlen,List.mem_flatMap]
  constructor
  · rintro ⟨j,hj,hv⟩
    have hj' : j < P.length e-1 := List.mem_range.mp hj
    rw [P.routeList_visit e ⟨j,hj'⟩] at hv
    exact ⟨⟨j,hj'⟩,hv⟩
  · rintro ⟨j,hj⟩
    refine ⟨j.val,List.mem_range.mpr j.isLt,?_⟩
    rw [P.routeList_visit e j]
    exact hj

end QMAPortRouteData
end ContinuumCoulomb

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
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

 theorem listedVisits_mem (es : List G.Edge) (hcover : ∀ e, e ∈ es) (v : Visit) :
    v ∈ P.listedVisits es ↔ v ∈ P.routingTable.2.1 := by
  change v ∈ P.listedVisits es ↔ v ∈ P.routingVisits
  simp only [listedVisits,List.mem_flatMap,P.routeList_visits_general,routingVisits,
    Finset.mem_toList,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨e,_,j,hj⟩
    exact ⟨⟨e,j⟩,hj⟩
  · rintro ⟨i,hi⟩
    exact ⟨i.1,hcover i.1,i.2,hi⟩

end QMAPortRouteData
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

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem permitted_bodies_disjoint
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (R S : QMACellRouteBody) (hR : P.RoutingAllowed R) (hS : P.RoutingAllowed S)
    (hvR : R.Valid) (hvS : S.Valid)
    (hne : s(R.source,R.target) ≠ s(S.source,S.target)) :
    Disjoint ((R.path.drop 1).dropLast).toFinset S.path.toFinset := by
  rcases qmaCellBody_cases R with ⟨p,e,rfl⟩ | ⟨p,a,b,c,rfl⟩
  · rcases qmaCellBody_cases S with ⟨q,f,rfl⟩ | ⟨q,d,f,g,rfl⟩
    · have hneq : p ≠ q ∨ e ≠ f := by
        by_cases hp : p = q
        · right
          intro he
          apply hne
          rw [hp,he]
        · exact Or.inl hp
      exact P.internal_bodies_disjoint havoid p q e f hneq hR hS
    · exact P.internal_corridor_disjoint p q e d f g hR hS
  · rcases qmaCellBody_cases S with ⟨q,e,rfl⟩ | ⟨q,d,f,g,rfl⟩
    · exact P.corridor_internal_disjoint p q a b c e hvR hR hS
    · have hd := P.corridors_disjoint p q a d b c f g hvR hvS hR hS hne
      apply Finset.disjoint_left.mpr
      intro z hz hw
      apply Finset.disjoint_left.mp hd _ hw
      exact List.mem_toFinset.mpr
        (List.mem_of_mem_drop (List.mem_of_mem_dropLast (List.mem_toFinset.mp hz)))

theorem permitted_routes_disjoint
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (R S : QMACellRoute) (hR : P.RoutingAllowed R.body) (hS : P.RoutingAllowed S.body)
    (hvR : R.Valid) (hvS : S.Valid) (hne : R.endpointPair ≠ S.endpointPair) :
    Disjoint ((R.path.drop 1).dropLast).toFinset S.path.toFinset := by
  rw [qmaRoute_interior_finset,qmaRoute_path_finset]
  apply P.permitted_bodies_disjoint havoid R.body S.body hR hS hvR hvS
  simpa only [QMACellRoute.endpointPair_body] using hne

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPermittedEndpointAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An interior point of a permitted path cannot be an endpoint of any other
permitted path, including catalog paths not present in the Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem permitted_avoids_source
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (R S : QMACellRoute) (hR : P.RoutingAllowed R.body) (hS : P.RoutingAllowed S.body)
    (hvR : R.Valid) (hvS : S.Valid) : S.source ∉ (R.path.drop 1).dropLast := by
  intro hz
  have hne : R.endpointPair ≠ S.endpointPair := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨ha,_⟩ | ⟨_,ha⟩
    · exact qmaListInterior_ne_head (R.simple hvR) R.endpoints.1 hz ha.symm
    · exact qmaListInterior_ne_last (R.simple hvR) R.endpoints.2 hz ha.symm
  have hSpath : S.source ∈ S.path := by
    obtain ⟨t,ht⟩ := List.head?_eq_some_iff.mp S.endpoints.1
    rw [ht]
    exact List.mem_cons_self
  exact Finset.disjoint_left.mp (P.permitted_routes_disjoint havoid R S hR hS hvR hvS hne)
    (List.mem_toFinset.mpr hz) (List.mem_toFinset.mpr hSpath)

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPhysicalEndpointCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every physical spin is an endpoint of a permitted catalog path. This also
covers isolated source spins and supplies the no-interior-spin condition. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical

theorem qmaPatchRoute_source_ancilla (p : ℕ × ℕ) :
    (qmaPatchRoute p 0).source = qmaGadgetAncilla p 0 := by
  change (32*p.1+10+4,32*p.2+10+8) = (32*p.1+14,32*p.2+18)
  apply Prod.ext <;> omega

theorem qmaPatchRoute_target_ancilla (p : ℕ × ℕ) :
    (qmaPatchRoute p 0).target = qmaGadgetAncilla p 1 := by
  change (32*p.1+10+8,32*p.2+10+4) = (32*p.1+18,32*p.2+14)
  apply Prod.ext <;> omega

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem physical_endpoint_cover (N : ℚ) (D : ℕ)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (v : Fin ((P.finishedGraph N D).n+P.crossingCells.card*2)) :
    ∃ R : QMACellRoute, P.RoutingAllowed R.body ∧ R.Valid ∧ R.source = P.crossingPosition N D v := by
  obtain ⟨v,rfl⟩ := (vertexEquiv (P.finishedGraph N D).n P.crossingCells.card).surjective v
  rcases v with v | ⟨i,a⟩
  · change ∃ R : QMACellRoute, P.RoutingAllowed R.body ∧ R.Valid ∧
      R.source = P.crossingPosition N D (old _ _ v)
    rw [P.crossingPosition_old]
    rcases P.iterate_position_kind N D v with ⟨p,hp⟩ | ⟨p,a,hp⟩
    · change P.finishedPosition N D v = qmaExpandedPoint p at hp
      have hs := P.finished_center_source N D v hp
      have hn : ¬P.IsCrossing p := by
        obtain ⟨w,rfl⟩ := hs
        exact P.source_not_crossing havoid w
      refine ⟨⟨.ray p 0,false⟩,⟨hs,hn⟩,trivial,?_⟩
      change qmaExpandedPoint p = qmaCrossingMove P.IsCrossing (P.finishedPosition N D v)
      rw [hp,qmaCrossingMove_center]
    · change P.finishedPosition N D v = qmaGridPort p a at hp
      have hpos := P.finished_port_cell_positive N D v hp
      let b := decide (P.IsCrossing p)
      let c := decide (P.IsCrossing (qmaGridNeighbor p a))
      refine ⟨⟨.corridor p a b c,false⟩,⟨rfl,rfl⟩,hpos,?_⟩
      change qmaCellTranslate p (qmaLocalPort b a) =
        qmaCrossingMove P.IsCrossing (P.finishedPosition N D v)
      rw [hp,qmaCrossingMove_port]
      exact (qmaMovedPort_local P.IsCrossing p a).symm
  · change ∃ R : QMACellRoute, P.RoutingAllowed R.body ∧ R.Valid ∧
      R.source = P.crossingPosition N D (fresh _ _ i a)
    rw [P.crossingPosition_fresh]
    have hc : P.IsCrossing (P.crossingCell i).val :=
      P.mem_crossingCells.mp (P.crossingCell i).property
    fin_cases a
    · exact ⟨qmaPatchRoute (P.crossingCell i).val 0,hc,trivial,qmaPatchRoute_source_ancilla _⟩
    · refine ⟨(qmaPatchRoute (P.crossingCell i).val 0).reverse,hc,trivial,?_⟩
      rw [QMACellRoute.reverse_source]
      exact qmaPatchRoute_target_ancilla _

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSelectedRoute
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal route selector returns a permitted catalog path for any
oriented pair of endpoints for which such a path exists. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
open QuantumRouteSelectorProgram QuantumTaggedRouteProgram QuantumFiniteRouteSearch

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def selectedAllowedRoute (x y : ℕ × ℕ) (h : P.HasAllowedRoute x y) : QMACellRoute :=
  (P.findAllowedRoute x y).get (P.findAllowedRoute_isSome h)

theorem selectedAllowedRoute_spec (x y : ℕ × ℕ) (h : P.HasAllowedRoute x y) :
    P.RoutingAllowed (P.selectedAllowedRoute x y h).body ∧
      (P.selectedAllowedRoute x y h).Valid ∧
      (P.selectedAllowedRoute x y h).source = x ∧
      (P.selectedAllowedRoute x y h).target = y := by
  have he : P.findAllowedRoute x y = some (P.selectedAllowedRoute x y h) :=
    (Option.some_get (P.findAllowedRoute_isSome h)).symm
  unfold findAllowedRoute at he
  have hp := List.find?_some he
  exact of_decide_eq_true hp

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPlanarSelectorTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite selector gives a planar family after arbitrary vertex
and edge permutations, including independent edge orientation changes. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

section Transport
variable (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    {H : QMARationalExchangeGraph}
    (vertex : Fin H.n ≃ Fin (P.crossingOutput N hD).merge.n)
    (edge : H.Edge ≃ (P.crossingOutput N hD).merge.Edge)
    (ends : ∀ e, s(vertex (H.left e),vertex (H.right e)) =
      s((P.crossingOutput N hD).merge.left (edge e),
        (P.crossingOutput N hD).merge.right (edge e)))

def selectorTransportRoute (e : H.Edge) : QMACellRoute :=
  P.selectedAllowedRoute (P.crossingPosition N D (vertex (H.left e)))
    (P.crossingPosition N D (vertex (H.right e)))
    (P.crossing_hasAllowedRoute N hD havoid _ _ (edge e) (ends e))

theorem selectorTransportRoute_spec (e : H.Edge) :
    P.RoutingAllowed (P.selectorTransportRoute N hD havoid vertex edge ends e).body ∧
      (P.selectorTransportRoute N hD havoid vertex edge ends e).Valid ∧
      (P.selectorTransportRoute N hD havoid vertex edge ends e).source =
        P.crossingPosition N D (vertex (H.left e)) ∧
      (P.selectorTransportRoute N hD havoid vertex edge ends e).target =
        P.crossingPosition N D (vertex (H.right e)) :=
  P.selectedAllowedRoute_spec _ _ _

theorem selectorTransportRoute_endpointPair (e : H.Edge) :
    (P.selectorTransportRoute N hD havoid vertex edge ends e).endpointPair =
      s(P.crossingPosition N D ((P.crossingOutput N hD).merge.left (edge e)),
        P.crossingPosition N D ((P.crossingOutput N hD).merge.right (edge e))) := by
  have hs := P.selectorTransportRoute_spec N hD havoid vertex edge ends e
  rw [QMACellRoute.endpointPair,hs.2.2.1,hs.2.2.2]
  rcases Sym2.eq_iff.mp (ends e) with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · rw [hl,hr]
  · rw [hl,hr]
    exact Sym2.eq_swap

theorem selectorTransportRoute_pairs_injective :
    Function.Injective (fun e =>
      (P.selectorTransportRoute N hD havoid vertex edge ends e).endpointPair) := by
  intro e f hef
  apply edge.injective
  apply qmaMergedEndpointPairs_injective (P.crossingOutput N hD)
    (P.crossingPosition N D) (P.crossingPosition_injective N D)
  exact (P.selectorTransportRoute_endpointPair N hD havoid vertex edge ends e).symm.trans
    (hef.trans (P.selectorTransportRoute_endpointPair N hD havoid vertex edge ends f))

def selectorPlanarList
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2) :
    QMAPlanarListData H where
  position v := P.crossingPosition N D (vertex v)
  position_injective := (P.crossingPosition_injective N D).comp vertex.injective
  path e := (P.selectorTransportRoute N hD havoid vertex edge ends e).path
  length e := (P.selectorTransportRoute N hD havoid vertex edge ends e).length_bounds.1
  first e := (P.selectorTransportRoute N hD havoid vertex edge ends e).endpoints.1.trans
    (congrArg some (P.selectorTransportRoute_spec N hD havoid vertex edge ends e).2.2.1)
  last e := (P.selectorTransportRoute N hD havoid vertex edge ends e).endpoints.2.trans
    (congrArg some (P.selectorTransportRoute_spec N hD havoid vertex edge ends e).2.2.2)
  simple e := (P.selectorTransportRoute N hD havoid vertex edge ends e).simple
    (P.selectorTransportRoute_spec N hD havoid vertex edge ends e).2.1
  step e := (P.selectorTransportRoute N hD havoid vertex edge ends e).chain
    (P.selectorTransportRoute_spec N hD havoid vertex edge ends e).2.1
  positive e z hz := by
    have hs := P.selectorTransportRoute_spec N hD havoid vertex edge ends e
    apply (P.selectorTransportRoute N hD havoid vertex edge ends e).path_positive ?_ ?_ hz
    · rw [hs.2.2.1]
      exact P.crossingPosition_positive hpositive N D _
    · rw [hs.2.2.2]
      exact P.crossingPosition_positive hpositive N D _
  avoids e v := by
    obtain ⟨R,ha,hv,hs⟩ := P.physical_endpoint_cover N D havoid (vertex v)
    rw [← hs]
    have he := P.selectorTransportRoute_spec N hD havoid vertex edge ends e
    exact P.permitted_avoids_source havoid _ R he.1 ha he.2.1 hv
  disjoint e f hef := by
    have he := P.selectorTransportRoute_spec N hD havoid vertex edge ends e
    have hf := P.selectorTransportRoute_spec N hD havoid vertex edge ends f
    exact P.permitted_routes_disjoint havoid _ _ he.1 hf.1 he.2.1 hf.2.1
      ((P.selectorTransportRoute_pairs_injective N hD havoid vertex edge ends).ne hef)

def selectorPlanarRoute
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2) :
    QMAPlanarRouteData H :=
  (P.selectorPlanarList N hD havoid vertex edge ends hpositive).toRoute

end Transport
end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepIndex
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Natural-number formulas for the checked row sweep. These formulas keep
the same operand order and insertion point as the physical circuit. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode

theorem rowCut_eq (width row : ℕ) (g : QMAGate) :
    qmaGateCut width (qmaSweepOrder width row) g=rowCut width row g := by
  cases g <;> simp [qmaGateCut,qmaGateSites,rowCut,gateTag,gateLeft,gateRight,
    sweepIndex_inverse,qmaQubit]

theorem rowStage_eq (rows width start : ℕ) (h : start < rows) (g : QMAGate) :
    qmaRowStage width (qmaGridWork rows width)
      (qmaGridQubit rows width ⟨start,by omega⟩)
      (qmaGridQubit rows width ⟨start+1,by omega⟩)
      (qmaSweepOrder width (rows-1-start)) g=rowStage rows width start g := by
  unfold qmaRowStage rowStage
  dsimp only
  rw [rowCut_eq,transferList_eq,transferList_eq,List.map_take,List.map_drop]
  have hp := rowPairs_eq rows width ⟨start,h⟩ (rows-1-start)
  simp only [Fin.castSucc_mk,Fin.succ_mk] at hp
  rw [hp,mapToRow_eq]

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

noncomputable def rowAddressProgram : Procedure tripleNatCode Nat.bits
    (fun x => rowAddress x.1 x.2.1 x.2.2) := by
  let w := Procedure.first Nat.bits (prodCode Nat.bits Nat.bits)
  let rest := Procedure.second Nat.bits (prodCode Nat.bits Nat.bits)
  let row := (Procedure.first Nat.bits Nat.bits).comp rest
  let i := (Procedure.second Nat.bits Nat.bits).comp rest
  let modulus := Procedure.successor.comp w
  exact Procedure.binaryAdd.comp ((Procedure.binaryMul.comp (row.pair modulus)).pair
    (Procedure.binaryMod.comp (i.pair modulus)))

noncomputable def mapToRowProgram : Procedure rowGateCode gateCode
    (fun x => mapToRow x.1 x.2.1 x.2.2) := by
  let w := Procedure.first Nat.bits (prodCode Nat.bits gateCode)
  let rest := Procedure.second Nat.bits (prodCode Nat.bits gateCode)
  let row := (Procedure.first Nat.bits gateCode).comp rest
  let gate := (Procedure.second Nat.bits gateCode).comp rest
  let left := rowAddressProgram.comp (w.pair (row.pair (gateLeftProgram.comp gate)))
  let right := rowAddressProgram.comp (w.pair (row.pair (gateRightProgram.comp gate)))
  let tag := gateTagProgram.comp gate
  let isH := Procedure.binaryZero.comp tag
  let isT := Procedure.binaryEq.comp (tag.pair (Procedure.constant rowGateCode Nat.bits 1))
  exact (Procedure.conditional isH (hadamardProgram.comp left)
    (Procedure.conditional isT (phaseProgram.comp left)
      (cnotProgram.comp (left.pair right)))).congrFun (by
        rintro ⟨w,row,g⟩
        cases g <;> rfl)

noncomputable def rowPairsProgram : Procedure rowPairsInputCode (listCode wirePairCode)
    (fun x => rowPairs x.1 x.2.1 x.2.2) := by
  let w := Procedure.first unaryCode (prodCode Nat.bits Nat.bits)
  let rest := Procedure.second unaryCode (prodCode Nat.bits Nat.bits)
  let wb := Procedure.unaryToBits.comp w
  let context := wb.pair rest
  let pointContext := Procedure.second unaryCode tripleNatCode
  let k := Procedure.unaryToBits.comp (Procedure.first unaryCode tripleNatCode)
  let pw := (Procedure.first Nat.bits (prodCode Nat.bits Nat.bits)).comp pointContext
  let pr := (Procedure.second Nat.bits (prodCode Nat.bits Nat.bits)).comp pointContext
  let row := (Procedure.first Nat.bits Nat.bits).comp pr
  let order := (Procedure.second Nat.bits Nat.bits).comp pr
  let index := sweepIndexProgram.comp (pw.pair (order.pair k))
  let modulus := Procedure.successor.comp pw
  let left := Procedure.binaryAdd.comp
    ((Procedure.binaryMul.comp (row.pair modulus)).pair index)
  let right := Procedure.binaryAdd.comp
    ((Procedure.binaryMul.comp ((Procedure.successor.comp row).pair modulus)).pair index)
  let point := left.pair right
  exact ((Procedure.tabulate (f := fun x k =>
    (x.2.1*(x.1+1)+sweepIndex x.1 x.2.2 k,
      (x.2.1+1)*(x.1+1)+sweepIndex x.1 x.2.2 k)) (0,0) point).comp
        ((Procedure.unarySuccessor.comp w).pair context)).congrFun (by intro x; rfl)

noncomputable def transferListProgram : Procedure (listCode wirePairCode) (listCode gateCode)
    transferList := by
  let left := Procedure.first Nat.bits Nat.bits
  let right := Procedure.second Nat.bits Nat.bits
  let forward := cnotProgram
  let backward := cnotProgram.comp (right.pair left)
  let nil := Procedure.constant wirePairCode (listCode gateCode) []
  let one := (Procedure.listCons gateCode).comp (forward.pair nil)
  let two := (Procedure.listCons gateCode).comp (backward.pair one)
  let three := (Procedure.listCons gateCode).comp (forward.pair two)
  exact ((QuantumRawExchange.flattenProgram gateCode (.hadamard 0)).comp
    (Procedure.listMap (0,0) [] three)).congrFun (by intro ps; rfl)

noncomputable def pairTakeProgram :
    Procedure (prodCode Nat.bits (listCode wirePairCode)) (listCode wirePairCode)
      (fun x => x.2.take x.1) := by
  let n := Procedure.first Nat.bits (listCode wirePairCode)
  let ps := Procedure.second Nat.bits (listCode wirePairCode)
  let len := (Procedure.listLength wirePairCode (0,0)).comp ps
  let count := Procedure.binarySub.comp (len.pair n)
  let reverse := (Procedure.listReverse wirePairCode (0,0)).comp ps
  exact ((Procedure.listReverse wirePairCode (0,0)).comp
    ((Procedure.listDrop wirePairCode).comp (count.pair reverse))).congrFun (by
      intro x
      simp only [Function.comp_apply,← List.reverse_take,List.reverse_reverse])

noncomputable def rowStageProgram : Procedure stageInputCode (listCode gateCode)
    (fun x => rowStage x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let rows := Procedure.first Nat.bits (prodCode unaryCode (prodCode Nat.bits gateCode))
  let tail := Procedure.second Nat.bits (prodCode unaryCode (prodCode Nat.bits gateCode))
  let width := (Procedure.first unaryCode (prodCode Nat.bits gateCode)).comp tail
  let rest := (Procedure.second unaryCode (prodCode Nat.bits gateCode)).comp tail
  let start := (Procedure.first Nat.bits gateCode).comp rest
  let gate := (Procedure.second Nat.bits gateCode).comp rest
  let order := Procedure.binarySub.comp
    ((Procedure.binarySub.comp (rows.pair
      (Procedure.constant stageInputCode Nat.bits 1))).pair start)
  let ps := rowPairsProgram.comp (width.pair (start.pair order))
  let cut := rowCutProgram.comp
    ((Procedure.unaryToBits.comp width).pair (order.pair gate))
  let front := transferListProgram.comp (pairTakeProgram.comp (cut.pair ps))
  let back := transferListProgram.comp ((Procedure.listDrop wirePairCode).comp (cut.pair ps))
  let mapped := mapToRowProgram.comp ((Procedure.unaryToBits.comp width).pair
    ((Procedure.successor.comp start).pair gate))
  let center := (Procedure.listCons gateCode).comp
    (mapped.pair (Procedure.constant stageInputCode (listCode gateCode) []))
  let first := (Procedure.listAppend gateCode (.hadamard 0)).comp (front.pair center)
  exact (Procedure.listAppend gateCode (.hadamard 0)).comp (first.pair back)

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete sweep is a finite table of the literal row stages, followed
by concatenation. It agrees with the recursive physical circuit. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram

theorem sweepList_eq (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) :
    qmaSweepCircuitFrom rows width start gs h=sweepList rows width start gs := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih =>
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    rw [sweepList_cons]
    simp only [qmaSweepCircuitFrom]
    rw [rowStage_eq rows width start hs,ih]

noncomputable def sweepListProgram : Procedure sweepInputCode (listCode gateCode)
    (fun x => sweepList x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let rest := Procedure.second Nat.bits (prodCode unaryCode (prodCode Nat.bits (listCode gateCode)))
  let tail := (Procedure.second unaryCode (prodCode Nat.bits (listCode gateCode))).comp rest
  let gates := (Procedure.second Nat.bits (listCode gateCode)).comp tail
  let context := Procedure.second unaryCode sweepInputCode
  let index := Procedure.unaryToBits.comp (Procedure.first unaryCode sweepInputCode)
  let rows := (Procedure.first Nat.bits (prodCode unaryCode (prodCode Nat.bits (listCode gateCode)))).comp context
  let cr := (Procedure.second Nat.bits (prodCode unaryCode (prodCode Nat.bits (listCode gateCode)))).comp context
  let width := (Procedure.first unaryCode (prodCode Nat.bits (listCode gateCode))).comp cr
  let ct := (Procedure.second unaryCode (prodCode Nat.bits (listCode gateCode))).comp cr
  let start := (Procedure.first Nat.bits (listCode gateCode)).comp ct
  let gs := (Procedure.second Nat.bits (listCode gateCode)).comp ct
  let gate := (Procedure.listGet gateCode (.hadamard 0)).comp (index.pair gs)
  let stage := rowStageProgram.comp
    (rows.pair (width.pair ((Procedure.binaryAdd.comp (start.pair index)).pair gate)))
  let table := Procedure.tabulate (f := fun (x : SweepInput) i =>
    rowStage x.1 x.2.1 (x.2.2.1+i) (readGate x.2.2.2 i)) [] stage
  exact ((QuantumRawExchange.flattenProgram gateCode (.hadamard 0)).comp
    (table.comp ((gateLengthProgram.comp gates).pair
      (Procedure.identity sweepInputCode)))).congrFun (by
        intro x
        simp only [Function.comp_apply,id_eq,sweepList,List.flatMap_def])

noncomputable def sweepCircuitProgram : Procedure circuitCode circuitCode qmaSweepCircuit := by
  let rows := gateLengthProgram.comp gatesProgram
  let count := Procedure.unaryAdd.comp
    (workProgram.pair (Procedure.unaryMul.comp
      (rows.pair (Procedure.unarySuccessor.comp workProgram))))
  let gates := sweepListProgram.comp ((Procedure.unaryToBits.comp rows).pair
    (workProgram.pair ((Procedure.constant circuitCode Nat.bits 0).pair gatesProgram)))
  exact (count.pair (witnessProgram.pair gates)).result (by
    intro c
    change prodCode unaryCode (prodCode unaryCode (listCode gateCode))
      (qmaGridWork c.gates.length c.work,c.witness,
        sweepList c.gates.length c.work 0 c.gates)=
      prodCode unaryCode (prodCode unaryCode (listCode gateCode))
        (qmaGridWork c.gates.length c.work,c.witness,
          qmaSweepCircuitFrom c.gates.length c.work 0 c.gates _)
    rw [sweepList_eq])

noncomputable def sparseCircuitProgram : Procedure circuitCode circuitCode qmaSparseCircuit :=
  sweepCircuitProgram.comp nearestCircuitProgram

end ContinuumCoulomb.QuantumCircuitCode

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

def qmaPreparedCircuit (c : QMACircuit) : QMACircuit :=
  qmaSparseCircuit (qmaNonemptyCircuit c)

namespace QuantumCircuitCode

noncomputable def preparedCircuitProgram : Procedure circuitCode circuitCode qmaPreparedCircuit :=
  sparseCircuitProgram.comp nonemptyProgram

end QuantumCircuitCode

end ContinuumCoulomb

end

end OAI
end


