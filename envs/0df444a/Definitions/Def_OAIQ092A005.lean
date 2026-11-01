-- Prove2me | Definitions.Def_OAIQ092A005
-- name    : OAIQ092A005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T19:50:53.743808+00:00
-- url     : https://prove2.me/theorems/99729ab8-50f5-4754-af3d-8a4d610467ba
-- title:
--   Definitions bundle OAIQ092A005 of the split of OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 461 declarations of OpenAI's Lean: 203 definitions, 8 inductive types or structures and 250 theorems. The definitions and types are `OAI.ContinuumCoulomb.HeatKernelModulus.density`, `OAI.ContinuumCoulomb.MediatorListProgram.envCode`, `OAI.ContinuumCoulomb.MediatorOffsetProgram.offsetCompBeta`, `OAI.ContinuumCoulomb.MediatorProgram.gProgram`, `OAI.ContinuumCoulomb.MediatorProgram.jProgram`, `OAI.ContinuumCoulomb.MediatorProgram.mediatorCompBeta`, `OAI.ContinuumCoulomb.MediatorProgram.precisionProgram`, `OAI.ContinuumCoulomb.MediatorProgram.rProgram`, `OAI.ContinuumCoulomb.MediatorProgram.rawCode`, `OAI.ContinuumCoulomb.MediatorProgram.wProgram`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.add`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.cube`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.cubicProduct`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.delta`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.double`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.finalBase`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.finalHead`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.finalN`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.finalWeight`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.finalWeightRaw`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.gProgram`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.mul`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.nProgram`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.nextN`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.powerTwoConstant`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.powerTwoStep`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.rCube`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.rProgram`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.restProgram`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.retainedBound`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.scale`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.scaleConstant`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.secondDelta`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.secondDeltaRaw`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.secondProgram`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.secondSpokes`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.secondSpokesRaw`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.sixR`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.spokeBound`, `OAI.ContinuumCoulomb.MediatorUnaryProgram.thirdBase` and 171 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/Computability, lean/OAI/MathematicalPhysics, in whole or in part: `Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich`, `ContinuumCoulomb_ManyBody_MediatorUnaryPrimitives`, `ContinuumCoulomb_ManyBody_MediatorUnaryScale`, `ContinuumCoulomb_ManyBody_MediatorUnarySecond`, `ContinuumCoulomb_ManyBody_MediatorUnaryThird`, `ContinuumCoulomb_OneParticle_HeatDensityModulus`, `ContinuumCoulomb_OneParticle_PlanarGapFromUniqueness`, `ContinuumCoulomb_OneParticle_PlanarGroundTransform`, `ContinuumCoulomb_OneParticle_PlanarGroundUniqueness`, `ContinuumCoulomb_OneParticle_PlanarLocalization`, `ContinuumCoulomb_OneParticle_PlanarModeDerivatives`, `ContinuumCoulomb_OneParticle_PlanarModeH1`, `ContinuumCoulomb_OneParticle_PlanarNearGroundCompactness`, `ContinuumCoulomb_OneParticle_PlanarProjectionGap`, `ContinuumCoulomb_OneParticle_PlanarSobolev`, `ContinuumCoulomb_OneParticle_PlanarSobolevDuality`, `ContinuumCoulomb_OneParticle_PlanarWellBottom`, `ContinuumCoulomb_OneParticle_VerticalSpectralInput`, `ContinuumCoulomb_Programs_MediatorListProgram`, `ContinuumCoulomb_Programs_MediatorOffsetProgram`, `ContinuumCoulomb_Programs_MediatorProgram`, `ContinuumCoulomb_Programs_MediatorUnaryProgram`, `ContinuumCoulomb_Programs_PrefactorCalibrationProgram`, `ContinuumCoulomb_Programs_SourceContactProgram`, `ContinuumCoulomb_Programs_SourceMetadataProgram`, `ContinuumCoulomb_Programs_SourceNormalizationProgram`, `ContinuumCoulomb_Quantum_QuantumAlgebraicScalarProgram`, `ContinuumCoulomb_Quantum_QuantumCellCrossings`, `ContinuumCoulomb_Quantum_QuantumCellMatching`, `ContinuumCoulomb_Quantum_QuantumCellPassages`, `ContinuumCoulomb_Quantum_QuantumCellPathProgram`, `ContinuumCoulomb_Quantum_QuantumCellPathTemplates`, `ContinuumCoulomb_Quantum_QuantumCellTranslate`, `ContinuumCoulomb_Quantum_QuantumCellVisitPaths`, `ContinuumCoulomb_Quantum_QuantumCorridorEndpoints`, `ContinuumCoulomb_Quantum_QuantumCorridorInterior`, `ContinuumCoulomb_Quantum_QuantumCorridorSeparation`, `ContinuumCoulomb_Quantum_QuantumCrossingMove`, `ContinuumCoulomb_Quantum_QuantumCrossingOutputRoutes`, `ContinuumCoulomb_Quantum_QuantumCrossingPairSupport`, `ContinuumCoulomb_Quantum_QuantumCrossingPatchChart`, `ContinuumCoulomb_Quantum_QuantumCrossingPlacement`, `ContinuumCoulomb_Quantum_QuantumCrossingSelectFromSites`, `ContinuumCoulomb_Quantum_QuantumCrossingSelection`, `ContinuumCoulomb_Quantum_QuantumCrossingSites`, `ContinuumCoulomb_Quantum_QuantumGateLocality`, `ContinuumCoulomb_Quantum_QuantumGridNeighborsFour`, `ContinuumCoulomb_Quantum_QuantumGridPorts`, `ContinuumCoulomb_Quantum_QuantumGridWalk`, `ContinuumCoulomb_Quantum_QuantumHalfCorridor`, `ContinuumCoulomb_Quantum_QuantumInflatedPath`, `ContinuumCoulomb_Quantum_QuantumInflatedSeparation`, `ContinuumCoulomb_Quantum_QuantumInnerPorts`, `ContinuumCoulomb_Quantum_QuantumInternalHalfSeparation`, `ContinuumCoulomb_Quantum_QuantumInternalRouteSeparation`, `ContinuumCoulomb_Quantum_QuantumListGraph`, `ContinuumCoulomb_Quantum_QuantumListPathStep`, `ContinuumCoulomb_Quantum_QuantumLocalCoordinates`, `ContinuumCoulomb_Quantum_QuantumLocalEnlarge`, `ContinuumCoulomb_Quantum_QuantumLocalJoin`, `ContinuumCoulomb_Quantum_QuantumLocalLift`, `ContinuumCoulomb_Quantum_QuantumManhattanRoute`, `ContinuumCoulomb_Quantum_QuantumManhattanSupport`, `ContinuumCoulomb_Quantum_QuantumMergeEdges`, `ContinuumCoulomb_Quantum_QuantumMergedOutputRoutes`, `ContinuumCoulomb_Quantum_QuantumPacketGeometry`, `ContinuumCoulomb_Quantum_QuantumPartialPaths`, `ContinuumCoulomb_Quantum_QuantumPatchEdgeCover`, `ContinuumCoulomb_Quantum_QuantumPatchPhysical`, `ContinuumCoulomb_Quantum_QuantumPathCoverage`, `ContinuumCoulomb_Quantum_QuantumPathCoverageReverse`, `ContinuumCoulomb_Quantum_QuantumPathEmbedding`, `ContinuumCoulomb_Quantum_QuantumPathPieces`, `ContinuumCoulomb_Quantum_QuantumPathPlacement`, `ContinuumCoulomb_Quantum_QuantumPathRelabeling`, `ContinuumCoulomb_Quantum_QuantumPathRelabelingIteration`, `ContinuumCoulomb_Quantum_QuantumPathRelabelingNext`, `ContinuumCoulomb_Quantum_QuantumPathRelabelingProperties`, `ContinuumCoulomb_Quantum_QuantumPathSchedule`, `ContinuumCoulomb_Quantum_QuantumPathTable`, `ContinuumCoulomb_Quantum_QuantumPathVisitCorrectness`, `ContinuumCoulomb_Quantum_QuantumPathVisitProgram`, `ContinuumCoulomb_Quantum_QuantumPhysicalCells`, `ContinuumCoulomb_Quantum_QuantumPlanarListData`, `ContinuumCoulomb_Quantum_QuantumPlanarRouteData`, `ContinuumCoulomb_Quantum_QuantumPlanarRouteRealization`, `ContinuumCoulomb_Quantum_QuantumPlanarSelectorTransport`, `ContinuumCoulomb_Quantum_QuantumPortCellPositive`, `ContinuumCoulomb_Quantum_QuantumPortChain`, `ContinuumCoulomb_Quantum_QuantumPortChainSeparation`, `ContinuumCoulomb_Quantum_QuantumPortCrossingSelection`, `ContinuumCoulomb_Quantum_QuantumPortGraphPairs`, `ContinuumCoulomb_Quantum_QuantumPortInnerPair`, `ContinuumCoulomb_Quantum_QuantumPortLinks`, `ContinuumCoulomb_Quantum_QuantumPortRaySupport`, `ContinuumCoulomb_Quantum_QuantumPortRouteData`, `ContinuumCoulomb_Quantum_QuantumPortSelectionProgram`, `ContinuumCoulomb_Quantum_QuantumPortSpinCoverage`, `ContinuumCoulomb_Quantum_QuantumRationalCrossing`, `ContinuumCoulomb_Quantum_QuantumRetainedCrossing`, `ContinuumCoulomb_Quantum_QuantumRetainedGeometry`, `ContinuumCoulomb_Quantum_QuantumRetainedRoutes`, `ContinuumCoulomb_Quantum_QuantumRouteEnumeration`, `ContinuumCoulomb_Quantum_QuantumRouteLeaf`, `ContinuumCoulomb_Quantum_QuantumRoutedSubdivision`, `ContinuumCoulomb_Quantum_QuantumRoutingCrossingTest`, `ContinuumCoulomb_Quantum_QuantumRoutingTableCorrectness`, `ContinuumCoulomb_Quantum_QuantumScaledDirection`, `ContinuumCoulomb_Quantum_QuantumScaledEdge`, `ContinuumCoulomb_Quantum_QuantumSelectedRoute`, `ContinuumCoulomb_Quantum_QuantumTaggedSupport`, `ContinuumCoulomb_Quantum_QuantumTranslatedInternalSeparation`, `ContinuumCoulomb_Quantum_QuantumUnaryForm`.
--
--   **Imports.** It imports the published bundle `Def_ContinuumCoulombHardness`; the bundles `OAIQ092A000`, `OAIQ092A001` and `OAIQ092A002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ092A008`, `OAIQ092A009`, `OAIQ092A012`, `OAIQ092A013`, `OAIQ092A014`, `OAIQ092A015` and `OAIQ092A016`; the statements `OAI_ContinuumCoulomb_ContactRationalGlobal_edge_error`, `OAI_ContinuumCoulomb_ContactRationalGlobal_local_end` and `OAI_ContinuumCoulomb_ContactRationalGlobal_local_start`; the proof of `OAI_ContinuumCoulomb_HubbardGlobal_actualHubbard_effectiveBottom`.
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
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
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
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
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
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
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
local instance instOpensMeasurableSpaceE_SobolevEuclideanRellich_r405c61_1 : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableAddE_SobolevEuclideanRellich_r405c61_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNegE_SobolevEuclideanRellich_r405c61_1 : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instFactOneLeTwo_SobolevEuclideanRellich
/-- The subspace of `H¹(volume)` whose `L²` component is (a.e.) supported in `K`.

We model “supported in `K`” as belonging to the closed range of the extension-by-zero map
`Lp(volume.restrict K) →ₗᵢ Lp(volume)`. -/
noncomputable def h1On (K : Set E) (hKm : MeasurableSet K) :
    Submodule ℝ (↥(h1 (μ := (volume : Measure E)) (E := E))) :=
  Submodule.comap
    (h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
    (LinearMap.range
      ((MeasureTheory.Lp.extendByZeroₗᵢ
          (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap))

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

def rawCode : Input → List Bool := prodCode unaryCode
  (prodCode unaryCode (prodCode unaryCode ratCode))

noncomputable def rProgram : Procedure rawCode unaryCode Prod.fst :=
  Procedure.first unaryCode (prodCode unaryCode (prodCode unaryCode ratCode))

noncomputable def wProgram : Procedure rawCode unaryCode (fun x => x.2.1) :=
  (Procedure.first unaryCode (prodCode unaryCode ratCode)).comp
    (Procedure.second unaryCode (prodCode unaryCode (prodCode unaryCode ratCode)))

noncomputable def gProgram : Procedure rawCode unaryCode (fun x => x.2.2.1) :=
  ((Procedure.first unaryCode ratCode).comp
    (Procedure.second unaryCode (prodCode unaryCode ratCode))).comp
      (Procedure.second unaryCode (prodCode unaryCode (prodCode unaryCode ratCode)))

noncomputable def jProgram : Procedure rawCode ratCode (fun x => x.2.2.2) :=
  ((Procedure.second unaryCode ratCode).comp
    (Procedure.second unaryCode (prodCode unaryCode ratCode))).comp
      (Procedure.second unaryCode (prodCode unaryCode (prodCode unaryCode ratCode)))

noncomputable def mediatorCompBeta {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : α → β} {g : β → γ} (q : Procedure eb ec g)
    (p : Procedure ea eb f) : Procedure ea ec (fun a => g (f a)) :=
  q.comp p

noncomputable def precisionProgram : Procedure rawCode unaryCode
    (fun x => MediatorParameters.precision x.1 x.2.2.1) :=
  (Procedure.unaryAdd.comp ((Procedure.unaryAdd.comp (rProgram.pair gProgram)).pair
    (Procedure.constant rawCode unaryCode 20))).congrFun (by intro x; rfl)

end ContinuumCoulomb.MediatorProgram

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

def envCode : Env → List Bool := prodCode unaryCode (prodCode unaryCode (prodCode unaryCode unaryCode))

end ContinuumCoulomb.MediatorListProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorUnaryPrimitives
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual unary arithmetic, projections, and a small repeated-doubling
program for the fixed mediator scale constant. -/

namespace ContinuumCoulomb.MediatorUnaryProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque add : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => x.1 + x.2) := Procedure.unaryAdd
noncomputable opaque mul : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => x.1 * x.2) := Procedure.unaryMul

noncomputable opaque rProgram : Procedure envCode unaryCode (fun x : Env => x.1) := Procedure.first _ _
noncomputable opaque restProgram : Procedure envCode (prodCode unaryCode (prodCode unaryCode unaryCode))
    (fun x : Env => x.2) := Procedure.second _ _
noncomputable opaque wProgram : Procedure envCode unaryCode (fun x : Env => x.2.1) :=
  (Procedure.first _ _).comp restProgram
noncomputable opaque gProgram : Procedure envCode unaryCode (fun x : Env => x.2.2.1) :=
  ((Procedure.first _ _).comp (Procedure.second _ _)).comp restProgram
noncomputable opaque nProgram : Procedure envCode unaryCode (fun x : Env => x.2.2.2) :=
  ((Procedure.second _ _).comp (Procedure.second _ _)).comp restProgram

noncomputable opaque cube : Procedure unaryCode unaryCode (fun n => n ^ 3) :=
  (mul.comp ((mul.comp
    ((Procedure.identity unaryCode).pair (Procedure.identity unaryCode))).pair
      (Procedure.identity unaryCode))).congrFun (by intro n; simp [pow_succ])

noncomputable opaque rCube : Procedure envCode unaryCode (fun x : Env => (x.1 + 1) ^ 3) :=
  cube.comp (Procedure.unarySuccessor.comp rProgram)
noncomputable opaque wCube : Procedure envCode unaryCode (fun x : Env => x.2.1 ^ 3) := cube.comp wProgram
noncomputable opaque cubicProduct : Procedure envCode unaryCode
    (fun x : Env => (x.1 + 1) ^ 3 * x.2.1 ^ 3) := mul.comp (rCube.pair wCube)
noncomputable opaque double : Procedure unaryCode unaryCode (fun n => 2 * n) :=
  (add.comp ((Procedure.identity unaryCode).pair
    (Procedure.identity unaryCode))).congrFun (by intro n; simp only [Function.comp_apply, id_eq]; omega)

/-- Emit the fixed scale constant by twenty doublings. This keeps the
finite machine description small instead of hardcoding a million pushes. -/
noncomputable opaque powerTwoStep (k : ℕ)
    (p : Procedure envCode unaryCode (fun _ => 2 ^ k)) :
    Procedure envCode unaryCode (fun _ => 2 ^ (k + 1)) :=
  (double.comp p).congrFun (by
    intro x
    simp only [Function.comp_apply, pow_succ]
    omega)

noncomputable def powerTwoConstant : (k : ℕ) → Procedure envCode unaryCode (fun _ => 2 ^ k)
  | 0 => Procedure.constant envCode unaryCode 1
  | k + 1 => powerTwoStep k (powerTwoConstant k)

noncomputable opaque scaleConstant : Procedure envCode unaryCode (fun _ => 1048576) :=
  (powerTwoConstant 20).congrFun (by intro x; norm_num)

end ContinuumCoulomb.MediatorUnaryProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorUnaryScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual unary programs for the polynomial mediator scale, its square,
and the retained-term and spoke coefficient bounds. -/

namespace ContinuumCoulomb.MediatorUnaryProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque scale : Procedure envCode unaryCode
    (fun x : Env => MediatorParameters.scale x.1 x.2.1 x.2.2.1) := by
  let product : Procedure envCode unaryCode
      (fun x : Env => (x.1 + 1) ^ 3 * x.2.1 ^ 3 * x.2.2.1) :=
    mul.comp (cubicProduct.pair gProgram)
  exact (mul.comp (scaleConstant.pair product)).congrFun
    (by intro x; simp only [Function.comp_apply, MediatorParameters.scale, Nat.mul_assoc])
noncomputable opaque delta : Procedure envCode unaryCode
    (fun x : Env => MediatorParameters.delta x.1 x.2.1 x.2.2.1) := by
  let square : Procedure envCode unaryCode (fun x : Env =>
      MediatorParameters.scale x.1 x.2.1 x.2.2.1 * MediatorParameters.scale x.1 x.2.1 x.2.2.1) :=
    mul.comp (scale.pair scale)
  exact square.congrFun (by
    intro x
    exact delta_as_mul x.1 x.2.1 x.2.2.1)

noncomputable opaque retainedBound : Procedure envCode unaryCode
    (fun x : Env => 3 * x.1 * MediatorParameters.delta x.1 x.2.1 x.2.2.1) := by
  let threeR : Procedure envCode unaryCode (fun x : Env => 3 * x.1) := mul.comp ((Procedure.constant envCode unaryCode 3).pair rProgram)
  exact mul.comp (threeR.pair delta)
noncomputable opaque spokeBound : Procedure envCode unaryCode
    (fun x : Env => 2 * MediatorParameters.scale x.1 x.2.1 x.2.2.1 * x.2.1) := by
  let twice : Procedure envCode unaryCode
      (fun x : Env => MediatorParameters.scale x.1 x.2.1 x.2.2.1 +
        MediatorParameters.scale x.1 x.2.1 x.2.2.1) := add.comp (scale.pair scale)
  exact (mul.comp (twice.pair wProgram)).congrFun (by intro x; simp only [Function.comp_apply, two_mul])
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

noncomputable opaque weightTwo : Procedure envCode unaryCode
    (fun x : Env => MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) := by
  let head : Procedure envCode unaryCode
      (fun x : Env => 2 + 3 * x.1 * MediatorParameters.delta x.1 x.2.1 x.2.2.1) :=
    add.comp ((Procedure.constant envCode unaryCode 2).pair retainedBound)
  let raw : Procedure envCode unaryCode
      (fun x : Env => 2 + 3 * x.1 * MediatorParameters.delta x.1 x.2.1 x.2.2.1 +
        2 * MediatorParameters.scale x.1 x.2.1 x.2.2.1 * x.2.1) :=
    add.comp (head.pair spokeBound)
  exact raw.congrFun (by intro x; rfl)

noncomputable opaque twiceR : Procedure envCode unaryCode (fun x : Env => 2 * x.1) :=
  (add.comp (rProgram.pair rProgram)).congrFun (by intro x; simp only [Function.comp_apply]; omega)
noncomputable opaque nextN : Procedure envCode unaryCode (fun x : Env => x.2.2.2 + 2 * x.1) :=
  add.comp (nProgram.pair twiceR)

noncomputable opaque secondProgram : Procedure envCode envCode secondEnv := by
  let raw : Procedure envCode envCode (fun x : Env =>
      (2 * x.1, MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1,
        x.2.2.1, x.2.2.2 + 2 * x.1)) :=
    twiceR.pair (weightTwo.pair (gProgram.pair nextN))
  exact raw.congrFun (by intro x; rfl)

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

noncomputable def unaryCompBeta {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : α → β} {g : β → γ} (q : Procedure eb ec g)
    (p : Procedure ea eb f) : Procedure ea ec (fun a => g (f a)) :=
  q.comp p

noncomputable opaque secondDeltaRaw : Procedure envCode unaryCode
    (fun a : Env => (fun x : Env => MediatorParameters.delta x.1 x.2.1 x.2.2.1) (secondEnv a)) := by
  let p := unaryCompBeta delta secondProgram
  exact p
noncomputable opaque secondDelta : Procedure envCode unaryCode (fun x : Env =>
    MediatorParameters.delta (2 * x.1) (MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) x.2.2.1) :=
  secondDeltaRaw.congrFun (fun x => deltaFn_apply (2 * x.1)
    (MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) x.2.2.1 (x.2.2.2 + 2 * x.1))
noncomputable opaque secondSpokesRaw : Procedure envCode unaryCode
    (fun a : Env => (fun x : Env => 2 * MediatorParameters.scale x.1 x.2.1 x.2.2.1 * x.2.1)
      (secondEnv a)) := by
  let p := unaryCompBeta spokeBound secondProgram
  exact p
noncomputable opaque secondSpokes : Procedure envCode unaryCode (fun x : Env =>
    2 * MediatorParameters.scale (2 * x.1) (MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) x.2.2.1 *
      MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) :=
  secondSpokesRaw.congrFun (fun x => spokeFn_apply (2 * x.1)
    (MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) x.2.2.1 (x.2.2.2 + 2 * x.1))
noncomputable opaque thirdBase : Procedure envCode unaryCode (fun x : Env =>
    2 + 3 * x.1 * MediatorParameters.delta x.1 x.2.1 x.2.2.1) :=
  add.comp ((Procedure.constant envCode unaryCode 2).pair retainedBound)
noncomputable opaque thirdHead : Procedure envCode unaryCode (fun x : Env =>
    2 + 3 * x.1 * MediatorParameters.delta x.1 x.2.1 x.2.2.1 +
      MediatorParameters.delta (2 * x.1) (MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) x.2.2.1) :=
  add.comp (thirdBase.pair secondDelta)
noncomputable opaque weightThreeRaw : Procedure envCode unaryCode (fun x : Env =>
    2 + 3 * x.1 * MediatorParameters.delta x.1 x.2.1 x.2.2.1 +
      MediatorParameters.delta (2 * x.1) (MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) x.2.2.1 +
      2 * MediatorParameters.scale (2 * x.1) (MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) x.2.2.1 *
        MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) :=
  add.comp (thirdHead.pair secondSpokes)
noncomputable opaque weightThree : Procedure envCode unaryCode
    (fun x : Env => MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) :=
  weightThreeRaw.congrFun (by intro x; rfl)

noncomputable opaque sixR : Procedure envCode unaryCode (fun x : Env => 6 * x.1) :=
  mul.comp ((Procedure.constant envCode unaryCode 6).pair rProgram)
noncomputable opaque thirdN : Procedure envCode unaryCode (fun x : Env => x.2.2.2 + 6 * x.1) :=
  add.comp (nProgram.pair sixR)

noncomputable opaque thirdProgramRaw : Procedure envCode envCode (fun x : Env =>
    (6 * x.1, MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1, x.2.2.1, x.2.2.2 + 6 * x.1)) :=
  sixR.pair (weightThree.pair (gProgram.pair thirdN))
noncomputable opaque thirdProgram : Procedure envCode envCode thirdEnv :=
  thirdProgramRaw.congrFun (by intro x; rfl)

end ContinuumCoulomb.MediatorUnaryProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarGroundTransform
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

def planarPartial (f : PlanarPosition → ℝ) (e : PlanarPosition) (x : PlanarPosition) : ℝ :=
  fderiv ℝ f x e

theorem planarPartial_continuous {v : PlanarPosition → ℝ} (hv : ContDiff ℝ 1 v)
    (e : PlanarPosition) : Continuous (planarPartial v e) :=
  ((hv.fderiv_right (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).clm_apply
    contDiff_const).continuous

theorem planarPartial_mul (phi v : PlanarPosition → ℝ)
    (hphi : ContDiff ℝ 1 phi) (hv : ContDiff ℝ 1 v) (e x : PlanarPosition) :
    planarPartial (fun y => phi y * v y) e x =
      phi x * planarPartial v e x + v x * planarPartial phi e x := by
  dsimp [planarPartial]
  rw [fderiv_fun_mul (hphi.differentiable (by norm_num) x) (hv.differentiable (by norm_num) x)]
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_HeatDensityModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit moduli of the actual forcing-weighted heat density. These
are the constants used for the fixed-dimensional quadrature mesh. -/

noncomputable section
namespace ContinuumCoulomb.HeatKernelModulus

def density (r : PlanarPosition) (t : ℝ) (p : PlanarPosition) : ℝ :=
  kernel t (‖r - p‖ ^ 2) * planarForcing p

end ContinuumCoulomb.HeatKernelModulus

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeDerivatives
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

def planarResolventOf (g : PlanarPosition → ℝ) (r : PlanarPosition) : ℝ :=
  ∫ b, planarResolventKernel b * g (r - b)

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

def originalIntegral (f : PlanarPosition → ℝ) : ℝ := ∫ x, f x

abbrev originalMeasurable : MeasurableSpace PlanarPosition := inferInstance

abbrev originalBorel : @BorelSpace PlanarPosition _ originalMeasurable := inferInstance

def originalIntegrable (f : PlanarPosition → ℝ) : Prop := Integrable f

theorem planar_integrable_change_borel
    (m : MeasurableSpace PlanarPosition) (hm : @BorelSpace PlanarPosition _ m)
    (f : PlanarPosition → ℝ) :
    (letI : MeasurableSpace PlanarPosition := m
     letI : BorelSpace PlanarPosition := hm
     letI : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace
     Integrable f) ↔ originalIntegrable f := by
  have he : m = originalMeasurable :=
    hm.measurable_eq.trans originalBorel.measurable_eq.symm
  cases he
  rfl

local instance instMeasurableSpacePlanarPosition : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instBorelSpacePlanarPosition : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instMeasureSpacePlanarPosition : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

abbrev Sobolev := RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
  (μ := (volume : Measure PlanarPosition)) (E := PlanarPosition)

abbrev Target := Lp ℝ 2 (volume : Measure PlanarPosition) ×
  Lp PlanarPosition 2 (volume : Measure PlanarPosition)

abbrev Test := RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c
  (E := PlanarPosition)

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

local instance instMeasurableSpacePlanarPosition_1 : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instBorelSpacePlanarPosition_1 : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instMeasureSpacePlanarPosition_1 : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

def cutoffBump : ContDiffBump (0 : PlanarPosition) := ⟨1, 2, by norm_num, by norm_num⟩

theorem cutoffBump_smooth : ContDiff ℝ ∞ (cutoffBump : PlanarPosition → ℝ) := cutoffBump.contDiff

def cutoff (n : ℕ) (x : PlanarPosition) : ℝ := cutoffBump (cutoffScale n • x)

theorem cutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (cutoff n) :=
  cutoffBump_smooth.comp (contDiff_const_smul (cutoffScale n))

theorem cutoff_nonnegative (n : ℕ) (x : PlanarPosition) : 0 ≤ cutoff n x := cutoffBump.nonneg

theorem cutoff_le_one (n : ℕ) (x : PlanarPosition) : cutoff n x ≤ 1 := cutoffBump.le_one

theorem cutoff_hasCompactSupport (n : ℕ) : HasCompactSupport (cutoff n) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : PlanarPosition) (2 * (n + 1 : ℝ)))
  intro x hx
  have hdist : 2 * (n + 1 : ℝ) < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  apply cutoffBump.zero_of_le_dist
  change 2 ≤ dist (cutoffScale n • x) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (cutoffScale_positive n)]
  change 2 ≤ (n + 1 : ℝ)⁻¹ * ‖x‖
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ (by positivity)).mpr hdist.le

theorem cutoff_tendsto (x : PlanarPosition) :
    Tendsto (fun n => cutoff n x) atTop (𝓝 1) := by
  have h := (cutoffBump_smooth.continuous.tendsto 0).comp
    (by simpa only [zero_smul] using cutoffScale_tendsto.smul_const x)
  have hzero : cutoffBump (0 : PlanarPosition) = 1 :=
    cutoffBump.one_of_mem_closedBall (by simp [cutoffBump])
  simpa only [Function.comp_def, cutoff, hzero] using h

theorem cutoff_fderiv (n : ℕ) (x : PlanarPosition) :
    fderiv ℝ (cutoff n) x = cutoffScale n • fderiv ℝ cutoffBump (cutoffScale n • x) := by
  have h := (cutoffBump_smooth.differentiable (by simp) (cutoffScale n • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul (cutoffScale n))
  change fderiv ℝ (cutoffBump ∘ fun y => cutoffScale n • y) x = _
  rw [h.fderiv]
  ext e
  simp

theorem cutoff_grad (n : ℕ) (x : PlanarPosition) :
    grad (cutoff n) x = cutoffScale n • grad cutoffBump (cutoffScale n • x) := by
  simp only [grad, cutoff_fderiv, map_smul]

theorem cutoff_grad_tendsto (x : PlanarPosition) :
    Tendsto (fun n => grad (cutoff n) x) atTop (𝓝 0) := by
  simp_rw [cutoff_grad]
  have h := ((continuous_grad (cutoffBump_smooth.of_le (by first | simp | exact_mod_cast le_top))).tendsto 0).comp
    (by simpa only [zero_smul] using cutoffScale_tendsto.smul_const x)
  simpa only [zero_smul, Function.comp_def] using cutoffScale_tendsto.smul h

theorem bump_grad_bounded : ∃ C : ℝ, ∀ x, ‖grad cutoffBump x‖ ≤ C :=
  (continuous_grad (cutoffBump_smooth.of_le (by first | simp | exact_mod_cast le_top))).bounded_above_of_compact_support
    (hasCompactSupport_grad cutoffBump.hasCompactSupport)

def cutoffGradBound : ℝ := Classical.choose bump_grad_bounded

theorem cutoffGradBound_nonnegative : 0 ≤ cutoffGradBound :=
  (norm_nonneg (grad cutoffBump 0)).trans (Classical.choose_spec bump_grad_bounded 0)

theorem cutoff_grad_bound (n : ℕ) (x : PlanarPosition) :
    ‖grad (cutoff n) x‖ ≤ cutoffGradBound := by
  rw [cutoff_grad, norm_smul, Real.norm_eq_abs, abs_of_pos (cutoffScale_positive n)]
  exact (mul_le_mul_of_nonneg_left (Classical.choose_spec bump_grad_bounded _)
    (cutoffScale_positive n).le).trans
    (mul_le_of_le_one_left cutoffGradBound_nonnegative (cutoffScale_le_one n))

theorem toLp_sub_norm_sq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {f g : PlanarPosition → F}
    (hf : MemLp f 2 (volume : Measure PlanarPosition))
    (hg : MemLp g 2 (volume : Measure PlanarPosition)) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, ‖f x - g x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
    with x hx hxf hxg
  simp only [real_inner_self_eq_norm_sq, hx, Pi.sub_apply, hxf, hxg]

theorem toLp_tendsto_of_integral_sub_sq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {f : ℕ → PlanarPosition → F} {g : PlanarPosition → F}
    (hf : ∀ n, MemLp (f n) 2 (volume : Measure PlanarPosition))
    (hg : MemLp g 2 (volume : Measure PlanarPosition))
    (hlim : Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hs : Tendsto (fun n => ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2) atTop (𝓝 0) := by
    simpa only [toLp_sub_norm_sq] using hlim
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero,
    dist_eq_norm] using hroot

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarLocalization
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

local instance instLocalizationMeasurable : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instLocalizationBorel : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instLocalizationMeasure : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

section LinearField
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

structure BoundedLinearField (F G : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] where
  value : PlanarPosition → F →L[ℝ] G
  continuous : Continuous value
  bound : ℝ
  bound_spec : ∀ x, ‖value x‖ ≤ bound

theorem BoundedLinearField.memLp (A : BoundedLinearField F G)
    (u : Lp F 2 (volume : Measure PlanarPosition)) :
    MemLp (fun x => A.value x (u x)) 2 := by
  apply (Lp.memLp u).of_le_mul (c := A.bound)
    (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
      A.continuous.aestronglyMeasurable (Lp.aestronglyMeasurable u))
  exact Filter.Eventually.of_forall (fun x => (A.value x).le_opNorm (u x) |>.trans
    (mul_le_mul_of_nonneg_right (A.bound_spec x) (norm_nonneg _)))

def BoundedLinearField.applyLp (A : BoundedLinearField F G)
    (u : Lp F 2 (volume : Measure PlanarPosition)) : Lp G 2 (volume : Measure PlanarPosition) :=
  (A.memLp u).toLp (fun x => A.value x (u x))

theorem BoundedLinearField.applyLp_ae (A : BoundedLinearField F G)
    (u : Lp F 2 (volume : Measure PlanarPosition)) :
    A.applyLp u =ᵐ[volume] fun x => A.value x (u x) := (A.memLp u).coeFn_toLp

def BoundedLinearField.linear (A : BoundedLinearField F G) :
    Lp F 2 (volume : Measure PlanarPosition) →ₗ[ℝ] Lp G 2 (volume : Measure PlanarPosition) where
  toFun := A.applyLp
  map_add' u v := by
    apply Lp.ext
    filter_upwards [A.applyLp_ae (u + v), A.applyLp_ae u, A.applyLp_ae v,
      Lp.coeFn_add u v, Lp.coeFn_add (A.applyLp u) (A.applyLp v)] with x h h₁ h₂ h₃ h₄
    simp only [h, h₄, h₃, Pi.add_apply, h₁, h₂, map_add]
  map_smul' c u := by
    apply Lp.ext
    change (A.applyLp (c • u) : PlanarPosition → G) =ᵐ[volume]
      (c • A.applyLp u : Lp G 2 volume)
    filter_upwards [A.applyLp_ae (c • u), A.applyLp_ae u,
      Lp.coeFn_smul c u, Lp.coeFn_smul c (A.applyLp u)] with x h h₁ h₂ h₃
    simp only [h, h₃, h₁, h₂, Pi.smul_apply, map_smul]

def BoundedLinearField.operator (A : BoundedLinearField F G) :
    Lp F 2 (volume : Measure PlanarPosition) →L[ℝ] Lp G 2 (volume : Measure PlanarPosition) :=
  A.linear.mkContinuous A.bound (fun u => Lp.norm_le_mul_norm_of_ae_le_mul (by
    filter_upwards [A.applyLp_ae u] with x hx
    change ‖A.applyLp u x‖ ≤ A.bound * ‖u x‖
    rw [hx]
    exact ((A.value x).le_opNorm (u x)).trans
      (mul_le_mul_of_nonneg_right (A.bound_spec x) (norm_nonneg _))))

end LinearField

theorem test_norm_bounded (h : Test) : ∃ B : ℝ, ∀ x, ‖h.val x‖ ≤ B :=
  h.property.1.continuous.bounded_above_of_compact_support h.property.2

theorem test_grad_bounded (h : Test) : ∃ B : ℝ, ∀ x, ‖grad h.val x‖ ≤ B :=
  (continuous_grad h.property.1).bounded_above_of_compact_support (hasCompactSupport_grad h.property.2)

def testNormBound (h : Test) : ℝ := Classical.choose (test_norm_bounded h)

theorem testNormBound_spec (h : Test) (x : PlanarPosition) : ‖h.val x‖ ≤ testNormBound h :=
  Classical.choose_spec (test_norm_bounded h) x

def testGradBound (h : Test) : ℝ := Classical.choose (test_grad_bounded h)

theorem testGradBound_spec (h : Test) (x : PlanarPosition) : ‖grad h.val x‖ ≤ testGradBound h :=
  Classical.choose_spec (test_grad_bounded h) x

def testScalarField (h : Test) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    BoundedLinearField F F where
  value x := h.val x • ContinuousLinearMap.id ℝ F
  continuous := h.property.1.continuous.smul continuous_const
  bound := testNormBound h
  bound_spec x := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg (h.val x))).trans
      (by simpa only [mul_one] using testNormBound_spec h x)

def testGradientField (h : Test) : BoundedLinearField ℝ PlanarPosition where
  value x := ContinuousLinearMap.toSpanSingleton ℝ (grad h.val x)
  continuous := (ContinuousLinearMap.toSpanSingletonLIE ℝ PlanarPosition).continuous.comp
    (continuous_grad h.property.1)
  bound := testGradBound h
  bound_spec x := by
    rw [ContinuousLinearMap.norm_toSpanSingleton]
    exact testGradBound_spec h x

def testTargetMultiplier (h : Test) : Target →L[ℝ] Target :=
  ((testScalarField h ℝ).operator.comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (((testScalarField h PlanarPosition).operator.comp (ContinuousLinearMap.snd ℝ _ _)) +
      ((testGradientField h).operator.comp (ContinuousLinearMap.fst ℝ _ _)))

def testProduct (h u : Test) : Test := ⟨fun x => h.val x * u.val x,
  ⟨h.property.1.mul u.property.1, h.property.2.mul_right⟩⟩

theorem mem_extendByZero_range {K : Set PlanarPosition} (hK : MeasurableSet K)
    (f : Lp ℝ 2 (volume : Measure PlanarPosition))
    (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    f ∈ LinearMap.range
      (Lp.extendByZeroₗᵢ (μ := volume) (E := ℝ) (p := 2) hK).toLinearMap := by
  let g : Lp ℝ 2 ((volume : Measure PlanarPosition).restrict K) :=
    ((Lp.memLp f).restrict K).toLp f
  have hg : ∀ᵐ x ∂volume, x ∈ K → g x = f x :=
    (ae_restrict_iff' hK).1 ((Lp.memLp f).restrict K).coeFn_toLp
  refine ⟨g, Lp.ext ?_⟩
  filter_upwards [Lp.extendByZeroₗᵢ_ae_eq hK g, hg, hf] with x he hgx hfx
  change Lp.extendByZeroₗᵢ hK g x = f x
  rw [he]
  by_cases hx : x ∈ K
  · simpa only [Set.indicator_of_mem hx] using hgx hx
  · simp only [Set.indicator_of_notMem hx, hfx hx]

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

local instance instMeasurableSpacePlanarPosition_2 : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instBorelSpacePlanarPosition_2 : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instMeasureSpacePlanarPosition_2 : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

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

local instance instMeasurableSpacePlanarPosition_3 : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instBorelSpacePlanarPosition_3 : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instMeasureSpacePlanarPosition_3 : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

end ContinuumCoulomb.PlanarSobolev

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarNearGroundCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness of normalized near-ground sequences for the actual well.
The positive free form makes compactness of the potential multiplier enough. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb.PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance instPlanarNearGroundCompactnessMeasurable : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instPlanarNearGroundCompactnessBorel : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instPlanarNearGroundCompactnessMeasure : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

end ContinuumCoulomb.PlanarSobolev

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarGapFromUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual planar well has a positive excitation gap once its zero-form
space is the line of the proved normalized ground mode. Compactness here is
proved directly, with no spectral or planar-gap input used. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb.PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance instPlanarGapFromUniquenessMeasurable : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instPlanarGapFromUniquenessBorel : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instPlanarGapFromUniquenessMeasure : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

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

local instance instPlanarSobolevDualityMeasurable : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instPlanarSobolevDualityBorel : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instPlanarSobolevDualityMeasure : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

end ContinuumCoulomb.PlanarSobolev

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarGroundUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniqueness and the actual manufactured planar ground gap, proved on the
full closed Sobolev graph without the published spectral hypothesis. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.PlanarSobolev

local instance instPlanarGroundUniquenessMeasurable : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instPlanarGroundUniquenessBorel : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instPlanarGroundUniquenessMeasure : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

end ContinuumCoulomb.PlanarSobolev

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalSpectralInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The published oscillator gap, specialized to the one-dimensional form.

Gerald Teschl, *Mathematical Methods in Quantum Mechanics*, second edition,
AMS Graduate Studies in Mathematics 157 (2014), Section 8.3, equations
(8.39)--(8.43) and Theorem 8.5; form-domain max-min in Theorem 4.12.
https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe2.pdf

The one-dimensional Hermite calculation gives eigenvalues `(2n+1)freq`
for `-∂²+freq²z²` and the Gaussian (8.41). Dividing by two gives bottom
`freq/2` and gap `freq`. We assume just the resulting projection-form inequality
on compact C¹ tests. The Gaussian and its normalization and attained energy
are actual definitions and proved facts, not extra premises. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def PublishedVerticalOscillatorGap : Prop :=
  ∀ (freq : ℝ), 0 < freq → ∀ (u : ℝ → ℝ), ContDiff ℝ 1 u → HasCompactSupport u →
    (3 * freq / 2) * (∫ z, u z ^ 2) - freq * (∫ z, u z * verticalMode freq z) ^ 2 ≤
      verticalForm freq u

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_MediatorUnaryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual final unary coefficient and vertex bounds, with the arithmetic
nodes kept separate from the fixed finite machine texts. -/

namespace ContinuumCoulomb.MediatorUnaryProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque thirdDeltaRaw : Procedure envCode unaryCode
    (fun a : Env => (fun x : Env => MediatorParameters.delta x.1 x.2.1 x.2.2.1) (thirdEnv a)) := by
  let p := unaryCompBeta delta thirdProgram
  exact p
noncomputable opaque thirdDelta : Procedure envCode unaryCode (fun x : Env =>
    MediatorParameters.delta (6 * x.1) (MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) x.2.2.1) :=
  thirdDeltaRaw.congrFun (fun x => deltaFn_apply (6 * x.1)
    (MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) x.2.2.1 (x.2.2.2 + 6 * x.1))
noncomputable opaque thirdSpokesRaw : Procedure envCode unaryCode
    (fun a : Env => (fun x : Env => 2 * MediatorParameters.scale x.1 x.2.1 x.2.2.1 * x.2.1)
      (thirdEnv a)) := by
  let p := unaryCompBeta spokeBound thirdProgram
  exact p
noncomputable opaque thirdSpokes : Procedure envCode unaryCode (fun x : Env =>
    2 * MediatorParameters.scale (6 * x.1) (MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) x.2.2.1 *
      MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) :=
  thirdSpokesRaw.congrFun (fun x => spokeFn_apply (6 * x.1)
    (MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) x.2.2.1 (x.2.2.2 + 6 * x.1))
noncomputable opaque finalBase : Procedure envCode unaryCode (fun x : Env =>
    2 + MediatorParameters.delta x.1 x.2.1 x.2.2.1) :=
  add.comp ((Procedure.constant envCode unaryCode 2).pair delta)
noncomputable opaque finalHead : Procedure envCode unaryCode (fun x : Env =>
    2 + MediatorParameters.delta x.1 x.2.1 x.2.2.1 +
      MediatorParameters.delta (6 * x.1) (MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) x.2.2.1) :=
  add.comp (finalBase.pair thirdDelta)
noncomputable opaque finalWeightRaw : Procedure envCode unaryCode (fun x : Env =>
    2 + MediatorParameters.delta x.1 x.2.1 x.2.2.1 +
      MediatorParameters.delta (6 * x.1) (MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) x.2.2.1 +
      2 * MediatorParameters.scale (6 * x.1) (MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) x.2.2.1 *
        MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) :=
  add.comp (finalHead.pair thirdSpokes)
noncomputable opaque finalWeight : Procedure envCode unaryCode
    (fun x : Env => MediatorParameters.finalWeight x.1 x.2.1 x.2.2.1) :=
  finalWeightRaw.congrFun (by intro x; rfl)

noncomputable opaque finalN : Procedure envCode unaryCode (fun x : Env => x.2.2.2 + 18 * x.1) :=
  add.comp (nProgram.pair (mul.comp
    ((Procedure.constant envCode unaryCode 18).pair rProgram)))

end ContinuumCoulomb.MediatorUnaryProgram

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

noncomputable def offsetCompBeta {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : α → β} {g : β → γ} (q : Procedure eb ec g)
    (p : Procedure ea eb f) : Procedure ea ec (fun a => g (f a)) :=
  q.comp p

end ContinuumCoulomb.MediatorOffsetProgram

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

noncomputable opaque precisionProgram (C : ℕ) : Procedure unaryCode unaryCode (precision C) :=
  Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode C).pair Procedure.unarySuccessor)

end ContinuumCoulomb.PrefactorCalibration

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

noncomputable opaque add : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => x.1 + x.2) := Procedure.unaryAdd

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

noncomputable opaque sizeProgram : Procedure binaryHeisenbergCodec.encode unaryCode size :=
  Procedure.unarySuccessor.comp (Procedure.length.precompose binaryHeisenbergCodec.encode)

end ContinuumCoulomb.SourceMetadataProgram

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

noncomputable opaque sizeProgram : Procedure binaryHeisenbergCodec.encode unaryCode size :=
  Procedure.unarySuccessor.comp SourceMetadataProgram.sizeProgram

noncomputable def powerProgram : (p : ℕ) → Procedure binaryHeisenbergCodec.encode unaryCode
    (fun d => size d ^ p)
  | 0 => Procedure.constant _ unaryCode 1
  | p+1 => (Procedure.unaryMul.comp ((powerProgram p).pair sizeProgram)).congrFun
      (by intro d; exact (pow_succ (size d) p).symm)

end ContinuumCoulomb.SourceContactProgram

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

abbrev QMAUnaryBasis (c : QMACircuit) :=
  SourceSpinBasis (c.gates.length+2) × SourceSpinBasis (c.work+1)

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

theorem qmaLocalLift_smul (S : Finset ι) (a : ℂ)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) :
    qmaLocalLift S (a • A) = a • qmaLocalLift S A := by
  simp [qmaLocalLift,Matrix.smul_kronecker,Matrix.submatrix_smul]

theorem qmaLocalLift_mul (S : Finset ι) (A B : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) :
    qmaLocalLift S (A*B) = qmaLocalLift S A*qmaLocalLift S B := by
  unfold qmaLocalLift
  rw [Matrix.submatrix_mul_equiv,←Matrix.mul_kronecker_mul,one_mul]

theorem QMALocalOn.mul {S : Finset ι} {A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) (hB : QMALocalOn S B) : QMALocalOn S (A*B) := by
  obtain ⟨a,rfl⟩ := hA
  obtain ⟨b,rfl⟩ := hB
  exact ⟨a*b,(qmaLocalLift_mul S a b).symm⟩

theorem QMALocalOn.smul {S : Finset ι} {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) (z : ℂ) : QMALocalOn S (z • A) := by
  obtain ⟨a,rfl⟩ := hA
  exact ⟨z • a,(qmaLocalLift_smul S z a).symm⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed verifier gates act on at most two actual qubits. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaGateSites (work : ℕ) : QMAGate → Finset (Fin (work+1))
  | .hadamard i => {qmaQubit work i}
  | .phaseT i => {qmaQubit work i}
  | .controlledNot i j => {qmaQubit work i,qmaQubit work j}

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

theorem QMALocalOn.mono {S T : Finset ι} (hST : S ⊆ T)
    {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ} (hA : QMALocalOn S A) : QMALocalOn T A := by
  obtain ⟨B,rfl⟩ := hA
  refine ⟨(fun u v => qmaLocalLift S B (qmaSupportExtend T u) (qmaSupportExtend T v)),?_⟩
  ext s t
  have hc (v : ι → Fin 2) :
      (fun i : {i // i ∈ S} => qmaSupportExtend T (fun j => v j.val) i.val) =
        (fun i : {i // i ∈ S} => v i.val) := by
    funext i
    simp only [qmaSupportExtend,dite_eq_left (hST i.property)]
  change B (fun i => s i.val) (fun i => t i.val)*
      (if (fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val) then 1 else 0) =
    (B (fun i : {i // i ∈ S} => qmaSupportExtend T (fun j => s j.val) i.val)
      (fun i : {i // i ∈ S} => qmaSupportExtend T (fun j => t j.val) i.val)*
      (if (fun i : {i // i ∉ S} => qmaSupportExtend T (fun j => s j.val) i.val) =
          (fun i : {i // i ∉ S} => qmaSupportExtend T (fun j => t j.val) i.val) then 1 else 0))*
      (if (fun i : {i // i ∉ T} => s i.val) = (fun i : {i // i ∉ T} => t i.val) then 1 else 0)
  rw [hc,hc]
  by_cases hr : (fun i : {i // i ∉ T} => s i.val) = (fun i : {i // i ∉ T} => t i.val)
  · have he :
        ((fun i : {i // i ∉ S} => qmaSupportExtend T (fun j => s j.val) i.val) =
          (fun i : {i // i ∉ S} => qmaSupportExtend T (fun j => t j.val) i.val)) ↔
        ((fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val)) := by
      constructor
      · intro h
        funext i
        by_cases hi : i.val ∈ T
        · simpa only [qmaSupportExtend,dite_eq_left hi] using congrFun h i
        · exact congrFun hr ⟨i.val,hi⟩
      · intro h
        funext i
        by_cases hi : i.val ∈ T
        · simpa only [qmaSupportExtend,dite_eq_left hi] using congrFun h i
        · simp only [qmaSupportExtend,dite_eq_right hi]
    simp only [ite_eq_left hr,mul_one,he]
  · have hs : (fun i : {i // i ∉ S} => s i.val) ≠ (fun i : {i // i ∉ S} => t i.val) := by
      intro h
      apply hr
      funext i
      exact congrFun h ⟨i.val,fun hi => i.property (hST hi)⟩
    rw [ite_eq_right hr,ite_eq_right hs,mul_zero,mul_zero]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalCoordinates
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem QMALocalOn.joinRight {κ : Type*} [Fintype κ] [DecidableEq κ]
    {S : Finset κ} {A : Matrix (κ → Fin 2) (κ → Fin 2) ℂ}
    (hA : QMALocalOn S A) :
    QMALocalOn (S.map (Function.Embedding.inr : κ ↪ ι ⊕ κ)) (qmaJoinMatrix (ι := ι) 1 A) := by
  obtain ⟨B,rfl⟩ := hA
  let T := S.map (Function.Embedding.inr : κ ↪ ι ⊕ κ)
  let k : {i // i ∈ S} → {i // i ∈ T} := fun i =>
    ⟨Sum.inr i.val,Finset.mem_map.mpr ⟨i.val,i.property,rfl⟩⟩
  refine ⟨(fun u v => B (u ∘ k) (v ∘ k)),?_⟩
  ext s t
  change (if (s ∘ Sum.inl) = (t ∘ Sum.inl) then (1:ℂ) else 0)*
    (B (fun i => s (Sum.inr i.val)) (fun i => t (Sum.inr i.val))*
      if (fun i : {i // i ∉ S} => s (Sum.inr i.val)) =
          (fun i : {i // i ∉ S} => t (Sum.inr i.val)) then 1 else 0) =
    B (fun i => s (Sum.inr i.val)) (fun i => t (Sum.inr i.val))*
      if (fun i : {i // i ∉ T} => s i.val) = (fun i : {i // i ∉ T} => t i.val) then 1 else 0
  have he : ((fun i : {i // i ∉ T} => s i.val) = (fun i : {i // i ∉ T} => t i.val)) ↔
      (s ∘ Sum.inl) = (t ∘ Sum.inl) ∧
      (fun i : {i // i ∉ S} => s (Sum.inr i.val)) =
        (fun i : {i // i ∉ S} => t (Sum.inr i.val)) := by
    constructor
    · intro h
      constructor
      · funext i
        exact congrFun h ⟨Sum.inl i,by simp [T]⟩
      · funext i
        exact congrFun h ⟨Sum.inr i.val,by simpa [T] using i.property⟩
    · rintro ⟨hl,hr⟩
      funext i
      rcases i with ⟨i,hi⟩
      cases i with
      | inl j => exact congrFun hl j
      | inr j => exact congrFun hr ⟨j,by simpa [T] using hi⟩
  by_cases hl : (s ∘ Sum.inl) = (t ∘ Sum.inl)
  <;> by_cases hr : (fun i : {i // i ∉ S} => s (Sum.inr i.val)) =
      (fun i : {i // i ∉ S} => t (Sum.inr i.val))
  <;> simp only [he,hl,hr,and_self,and_false,false_and,ite_true, if_true,ite_false, if_false,mul_one,
    one_mul,zero_mul,mul_zero]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalJoin
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem QMALocalOn.joinLeft {S : Finset ι} {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) :
    QMALocalOn (S.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)) (qmaJoinMatrix A (κ := κ) 1) := by
  obtain ⟨B,rfl⟩ := hA
  let T := S.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)
  let k : {i // i ∈ S} → {i // i ∈ T} := fun i =>
    ⟨Sum.inl i.val,Finset.mem_map.mpr ⟨i.val,i.property,rfl⟩⟩
  refine ⟨(fun u v => B (u ∘ k) (v ∘ k)),?_⟩
  ext s t
  change (B (fun i => s (Sum.inl i.val)) (fun i => t (Sum.inl i.val))*
      if (fun i : {i // i ∉ S} => s (Sum.inl i.val)) =
        (fun i : {i // i ∉ S} => t (Sum.inl i.val)) then 1 else 0)*
      (if (s ∘ Sum.inr) = (t ∘ Sum.inr) then (1:ℂ) else 0) =
    B (fun i => s (Sum.inl i.val)) (fun i => t (Sum.inl i.val))*
      if (fun i : {i // i ∉ T} => s i.val) = (fun i : {i // i ∉ T} => t i.val) then 1 else 0
  have he : ((fun i : {i // i ∉ T} => s i.val) = (fun i : {i // i ∉ T} => t i.val)) ↔
      (fun i : {i // i ∉ S} => s (Sum.inl i.val)) =
        (fun i : {i // i ∉ S} => t (Sum.inl i.val)) ∧ (s ∘ Sum.inr) = (t ∘ Sum.inr) := by
    constructor
    · intro h
      constructor
      · funext i
        exact congrFun h ⟨Sum.inl i.val,by simpa [T] using i.property⟩
      · funext i
        exact congrFun h ⟨Sum.inr i,by simp [T]⟩
    · rintro ⟨hl,hr⟩
      funext i
      rcases i with ⟨i,hi⟩
      cases i with
      | inl j => exact congrFun hl ⟨j,by simpa [T] using hi⟩
      | inr j => exact congrFun hr j
  by_cases hl : (fun i : {i // i ∉ S} => s (Sum.inl i.val)) =
      (fun i : {i // i ∉ S} => t (Sum.inl i.val))
  <;> by_cases hr : (s ∘ Sum.inr) = (t ∘ Sum.inr)
  <;> simp only [he,hl,hr,and_self,and_false,false_and,ite_true, if_true,ite_false, if_false,mul_one,mul_zero]

theorem QMALocalOn.join {S : Finset ι} {T : Finset κ}
    {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ} {B : Matrix (κ → Fin 2) (κ → Fin 2) ℂ}
    (hA : QMALocalOn S A) (hB : QMALocalOn T B) :
    QMALocalOn (S.map Function.Embedding.inl ∪ T.map Function.Embedding.inr) (qmaJoinMatrix A B) := by
  have he : qmaJoinMatrix A B = qmaJoinMatrix A (κ := κ) 1*qmaJoinMatrix (ι := ι) 1 B := by
    rw [← qmaJoinMatrix_mul,mul_one,one_mul]
  rw [he]
  exact (hA.joinLeft.mono Finset.subset_union_left).mul
    (hB.joinRight.mono Finset.subset_union_right)

end ContinuumCoulomb

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

def realCode : RealScalar → List Bool := prodCode ratCode ratCode
def scalarCode : Scalar → List Bool := prodCode realCode realCode

noncomputable opaque imagPartProgram : Procedure scalarCode scalarCode imagPart :=
  (Procedure.second realCode realCode).pair (Procedure.constant scalarCode realCode (realRat 0))

end ContinuumCoulomb.QuantumAlgebraicScalar

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTaggedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every column label gives an explicit bounded spatial support for its gate. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def QMALocatedGate (rows width : ℕ) (r : Fin (rows+1)) (j : Fin (width+1)) (g : QMAGate) : Prop :=
  ∀ k ∈ qmaGateSites (qmaGridWork rows width) g,
    ∃ s : Fin (rows+1), ∃ i : Fin (width+1),
      k = qmaGridQubit rows width s i ∧ r.val ≤ s.val ∧ s.val ≤ r.val+1 ∧
        i.val ≤ j.val+1 ∧ j.val ≤ i.val+1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumManhattanRoute
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.qmaFineRoute_last _root_.OAI.ContinuumCoulomb.qmaFineRoute_nat _root_.OAI.ContinuumCoulomb.qmaFineRoute_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short, simple lattice paths between the bounded-density fine-grid sites. -/

namespace ContinuumCoulomb

theorem qmaAxisWalk_distance (a b k : ℕ) (hk : k ≤ Nat.dist a b) :
    Nat.dist a (qmaAxisWalk a b k) = k := by
  unfold qmaAxisWalk Nat.dist at *
  split_ifs <;> omega

theorem qmaAxisWalk_step (a b k : ℕ) (hk : k < Nat.dist a b) :
    Nat.dist (qmaAxisWalk a b k) (qmaAxisWalk a b (k+1)) = 1 := by
  unfold qmaAxisWalk Nat.dist at *
  split_ifs <;> omega

theorem qmaManhattanPoint_distance (p q : ℕ × ℕ) (k : ℕ) (hk : k ≤ qmaManhattanLength p q) :
    Nat.dist p.1 (qmaManhattanPoint p q k).1+
      Nat.dist p.2 (qmaManhattanPoint p q k).2 = k := by
  by_cases hx : k ≤ Nat.dist p.1 q.1
  · simp [qmaManhattanPoint,hx,qmaAxisWalk_distance _ _ _ hx]
  · have hy : k-Nat.dist p.1 q.1 ≤ Nat.dist p.2 q.2 := by unfold qmaManhattanLength at hk; omega
    simp only [qmaManhattanPoint,hx,ite_false, if_false]
    rw [qmaAxisWalk_distance _ _ _ hy]
    omega

theorem qmaManhattanPoint_step (p q : ℕ × ℕ) (k : ℕ) (hk : k < qmaManhattanLength p q) :
    Nat.dist (qmaManhattanPoint p q k).1 (qmaManhattanPoint p q (k+1)).1+
      Nat.dist (qmaManhattanPoint p q k).2 (qmaManhattanPoint p q (k+1)).2 = 1 := by
  by_cases hx : k < Nat.dist p.1 q.1
  · have hx0 : k ≤ Nat.dist p.1 q.1 := by omega
    have hx1 : k+1 ≤ Nat.dist p.1 q.1 := by omega
    simp [qmaManhattanPoint,hx0,hx1,qmaAxisWalk_step _ _ _ hx]
  · by_cases he : k = Nat.dist p.1 q.1
    · subst k
      have hy : 0 < Nat.dist p.2 q.2 := by unfold qmaManhattanLength at hk; omega
      simpa [qmaManhattanPoint] using qmaAxisWalk_step p.2 q.2 0 hy
    · have hx0 : ¬k ≤ Nat.dist p.1 q.1 := by omega
      have hx1 : ¬k+1 ≤ Nat.dist p.1 q.1 := by omega
      have hy : k-Nat.dist p.1 q.1 < Nat.dist p.2 q.2 := by unfold qmaManhattanLength at hk; omega
      have hs : k+1-Nat.dist p.1 q.1 = (k-Nat.dist p.1 q.1)+1 := by omega
      simp [qmaManhattanPoint,hx0,hx1,hs,qmaAxisWalk_step _ _ _ hy]

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite unit-step route has a simple subroute with no larger length. -/

namespace ContinuumCoulomb

theorem qmaManhattanPoint_adj (p q : ℕ × ℕ) (k : ℕ)
    (hk : k < qmaManhattanLength p q) :
    qmaSquareGrid.Adj (qmaManhattanPoint p q k) (qmaManhattanPoint p q (k+1)) :=
  qmaManhattanPoint_step p q k hk

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

theorem qmaGridNeighbor_exists {p q : ℕ × ℕ} (ha : qmaSquareGrid.Adj p q) :
    ∃ a : Fin 4, qmaGridNeighbor p a = q := by
  change Nat.dist p.1 q.1 + Nat.dist p.2 q.2 = 1 at ha
  have h : (q.1 = p.1+1 ∧ q.2 = p.2) ∨ (q.1 = p.1 ∧ q.2 = p.2+1) ∨
      (q.1+1 = p.1 ∧ q.2 = p.2) ∨ (q.1 = p.1 ∧ q.2+1 = p.2) := by
    unfold Nat.dist at ha
    omega
  rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact ⟨0,Prod.ext hx.symm hy.symm⟩
  · exact ⟨1,Prod.ext hx.symm hy.symm⟩
  · refine ⟨2,?_⟩
    apply Prod.ext <;> simp [qmaGridNeighbor] <;> omega
  · refine ⟨3,?_⟩
    apply Prod.ext <;> simp [qmaGridNeighbor] <;> omega

theorem qmaGridNeighborIndex_spec {p q : ℕ × ℕ} (hx : 0 < p.1) (hy : 0 < p.2)
    (ha : qmaSquareGrid.Adj p q) : qmaGridNeighbor p (qmaGridNeighborIndex p q) = q := by
  obtain ⟨a,rfl⟩ := qmaGridNeighbor_exists ha
  rcases p with ⟨x,y⟩
  have hs : x-1+1 = x := by omega
  fin_cases a <;> simp [qmaGridNeighborIndex,qmaGridNeighbor,hs]

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridPorts
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.qmaPointCell_center _root_.OAI.ContinuumCoulomb.qmaPointCell_port _root_.OAI.ContinuumCoulomb.qmaPortChain_last _root_.OAI.ContinuumCoulomb.qmaPortChain_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct entry and exit spin locations for every grid cell. -/

namespace ContinuumCoulomb

theorem qmaGridPort_injective : Function.Injective (fun x : (ℕ × ℕ) × Fin 4 => qmaGridPort x.1 x.2) := by
  rintro ⟨p,a⟩ ⟨q,b⟩ h
  have he := congrArg (fun z : ℕ × ℕ => (z.1/32,z.2/32)) h
  simp only [qmaGridPort_cell] at he
  subst q
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  have hab : a = b := by
    fin_cases a <;> fin_cases b <;> simp [qmaGridPort] at hx hy ⊢
  subst b
  rfl

theorem qmaGridPort_ne_center (p q : ℕ × ℕ) (a : Fin 4) : qmaGridPort p a ≠ qmaExpandedPoint q := by
  intro h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases a <;> simp [qmaGridPort,qmaExpandedPoint] at hx hy <;> omega

theorem qmaExpandedPoint_injective : Function.Injective qmaExpandedPoint := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext <;> simp only [qmaExpandedPoint] at hx hy <;> omega

theorem qmaDirectedPort_injective {p q r s : ℕ × ℕ}
    (hp : 0 < p.1 ∧ 0 < p.2) (hr : 0 < r.1 ∧ 0 < r.2)
    (hpq : qmaSquareGrid.Adj p q) (hrs : qmaSquareGrid.Adj r s)
    (h : qmaDirectedPort p q = qmaDirectedPort r s) : p = r ∧ q = s := by
  have he : (p,qmaGridNeighborIndex p q) = (r,qmaGridNeighborIndex r s) := qmaGridPort_injective h
  constructor
  · exact congrArg Prod.fst he
  · have hh := congrArg (fun z : (ℕ × ℕ) × Fin 4 => qmaGridNeighbor z.1 z.2) he
    simpa only [qmaGridNeighborIndex_spec hp.1 hp.2 hpq,qmaGridNeighborIndex_spec hr.1 hr.2 hrs] using hh

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortChain
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.qmaPointCell_center _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each coarse route is replaced by its ordered incoming and outgoing cell ports. -/

namespace ContinuumCoulomb

theorem qmaPortChain_inner (p : ℕ → ℕ × ℕ) {L k : ℕ} (hk0 : 0 < k) (hk : k < 2*L+1) :
    qmaPortChain p L k = qmaRoutePort p k := by
  simp [qmaPortChain,show k ≠ 0 from by omega,show k ≠ 2*L+1 from by omega]

theorem qmaPortNeighborIndex_bounds {L k : ℕ} (_hk0 : 0 < k) (hk : k < 2*L+1) :
    k/2 ≤ L ∧ qmaPortNeighborIndex k ≤ L := by
  unfold qmaPortNeighborIndex
  split_ifs <;> omega

theorem qmaPortNeighborIndex_injective {L i j : ℕ} (hi0 : 0 < i) (_hi : i < 2*L+1)
    (hj0 : 0 < j) (_hj : j < 2*L+1) (hd : i/2 = j/2)
    (hn : qmaPortNeighborIndex i = qmaPortNeighborIndex j) : i = j := by
  unfold qmaPortNeighborIndex at hn
  split_ifs at hn <;> omega

theorem qmaRoutePort_adjacent (p : ℕ → ℕ × ℕ) {L k : ℕ}
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1))) (hk0 : 0 < k) (hk : k < 2*L+1) :
    qmaSquareGrid.Adj (p (k/2)) (p (qmaPortNeighborIndex k)) := by
  by_cases h : k%2 = 1
  · simp only [qmaPortNeighborIndex,h,ite_true, if_true]
    exact hp (k/2) (by omega)
  · simp only [qmaPortNeighborIndex,h,ite_false, if_false]
    have he : k/2-1+1 = k/2 := by omega
    have ha := hp (k/2-1) (by omega)
    rw [he] at ha
    exact ha.symm

theorem qmaPortChain_inner_not_center (p : ℕ → ℕ × ℕ) {L k : ℕ}
    (hk0 : 0 < k) (hk : k < 2*L+1) (q : ℕ × ℕ) : qmaPortChain p L k ≠ qmaExpandedPoint q := by
  rw [qmaPortChain_inner p hk0 hk]
  exact qmaGridPort_ne_center _ _ _

theorem qmaPortChain_inner_injective (p : ℕ → ℕ × ℕ) {L : ℕ}
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1)))
    (hpos : ∀ i ≤ L, 0 < (p i).1 ∧ 0 < (p i).2)
    (hs : ∀ i j, i ≤ L → j ≤ L → p i = p j → i = j)
    {i j : ℕ} (hi0 : 0 < i) (hi : i < 2*L+1) (hj0 : 0 < j) (hj : j < 2*L+1)
    (h : qmaPortChain p L i = qmaPortChain p L j) : i = j := by
  rw [qmaPortChain_inner p hi0 hi,qmaPortChain_inner p hj0 hj] at h
  obtain ⟨hiB,hiN⟩ := qmaPortNeighborIndex_bounds hi0 hi
  obtain ⟨hjB,hjN⟩ := qmaPortNeighborIndex_bounds hj0 hj
  have he := qmaDirectedPort_injective (hpos _ hiB) (hpos _ hjB)
    (qmaRoutePort_adjacent p hp hi0 hi) (qmaRoutePort_adjacent p hp hj0 hj) h
  exact qmaPortNeighborIndex_injective hi0 hi hj0 hj (hs _ _ hiB hjB he.1) (hs _ _ hiN hjN he.2)

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortChainSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Port chains are simple and remain disjoint even where coarse routes meet. -/

namespace ContinuumCoulomb

theorem qmaPortChain_injective (p : ℕ → ℕ × ℕ) {L : ℕ} (hL : 0 < L)
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1)))
    (hpos : ∀ i ≤ L, 0 < (p i).1 ∧ 0 < (p i).2)
    (hs : ∀ i j, i ≤ L → j ≤ L → p i = p j → i = j)
    {i j : ℕ} (hi : i ≤ 2*L+1) (hj : j ≤ 2*L+1)
    (h : qmaPortChain p L i = qmaPortChain p L j) : i = j := by
  by_cases hi0 : i = 0
  · subst i
    by_cases hj0 : j = 0
    · exact hj0.symm
    by_cases hjL : j = 2*L+1
    · subst j
      rw [qmaPortChain_zero,qmaPortChain_last] at h
      have hz := hs 0 L (Nat.zero_le _) le_rfl (qmaExpandedPoint_injective h)
      omega
    · simp only [qmaPortChain_zero] at h
      exact (qmaPortChain_inner_not_center p (L := L) (by omega) (by omega) _ h.symm).elim
  by_cases hiL : i = 2*L+1
  · subst i
    by_cases hj0 : j = 0
    · subst j
      rw [qmaPortChain_zero,qmaPortChain_last] at h
      have hz := hs L 0 le_rfl (Nat.zero_le _) (qmaExpandedPoint_injective h)
      omega
    by_cases hjL : j = 2*L+1
    · exact hjL.symm
    · simp only [qmaPortChain_last] at h
      exact (qmaPortChain_inner_not_center p (L := L) (by omega) (by omega) _ h.symm).elim
  by_cases hj0 : j = 0
  · subst j
    simp only [qmaPortChain_zero] at h
    exact (qmaPortChain_inner_not_center p (L := L) (by omega) (by omega) _ h).elim
  by_cases hjL : j = 2*L+1
  · subst j
    simp only [qmaPortChain_last] at h
    exact (qmaPortChain_inner_not_center p (L := L) (by omega) (by omega) _ h).elim
  exact qmaPortChain_inner_injective p hp hpos hs (by omega) (by omega) (by omega) (by omega) h

theorem qmaPortChain_interiors_disjoint (p q : ℕ → ℕ × ℕ) {L M : ℕ}
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1)))
    (hq : ∀ i < M, qmaSquareGrid.Adj (q i) (q (i+1)))
    (hp0 : ∀ i ≤ L, 0 < (p i).1 ∧ 0 < (p i).2)
    (hq0 : ∀ j ≤ M, 0 < (q j).1 ∧ 0 < (q j).2)
    (he : ∀ i j, i < L → j < M →
      ¬(p i = q j ∧ p (i+1) = q (j+1)) ∧ ¬(p i = q (j+1) ∧ p (i+1) = q j))
    {i j : ℕ} (hi0 : 0 < i) (hi : i < 2*L+1) (hj : j ≤ 2*M+1) :
    qmaPortChain p L i ≠ qmaPortChain q M j := by
  intro h
  by_cases hj0 : j = 0
  · subst j
    simp only [qmaPortChain_zero] at h
    exact (qmaPortChain_inner_not_center p hi0 hi _ h).elim
  by_cases hjM : j = 2*M+1
  · subst j
    simp only [qmaPortChain_last] at h
    exact (qmaPortChain_inner_not_center p hi0 hi _ h).elim
  have hj' : j < 2*M+1 := by omega
  rw [qmaPortChain_inner p hi0 hi,qmaPortChain_inner q (by omega) hj'] at h
  obtain ⟨hib,_⟩ := qmaPortNeighborIndex_bounds hi0 hi
  obtain ⟨hjb,_⟩ := qmaPortNeighborIndex_bounds (by omega : 0 < j) hj'
  have hc := qmaDirectedPort_injective (hp0 _ hib) (hq0 _ hjb)
    (qmaRoutePort_adjacent p hp hi0 hi) (qmaRoutePort_adjacent q hq (by omega) hj') h
  by_cases hie : i%2 = 1 <;> by_cases hje : j%2 = 1
  · simp only [qmaPortNeighborIndex,hie,hje,ite_true, if_true] at hc
    exact (he (i/2) (j/2) (by omega) (by omega)).1 hc
  · simp only [qmaPortNeighborIndex,hie,hje,ite_true, if_true,ite_false, if_false] at hc
    have hjp : j/2-1+1 = j/2 := by omega
    apply (he (i/2) (j/2-1) (by omega) (by omega)).2
    simpa only [hjp] using hc
  · simp only [qmaPortNeighborIndex,hie,hje,ite_true, if_true,ite_false, if_false] at hc
    have hip : i/2-1+1 = i/2 := by omega
    apply (he (i/2-1) (j/2) (by omega) (by omega)).2
    simpa only [hip] using And.intro hc.2 hc.1
  · simp only [qmaPortNeighborIndex,hie,hje,ite_false, if_false] at hc
    have hip : i/2-1+1 = i/2 := by omega
    have hjp : j/2-1+1 = j/2 := by omega
    apply (he (i/2-1) (j/2-1) (by omega) (by omega)).1
    simpa only [hip,hjp] using And.intro hc.2 hc.1

end ContinuumCoulomb

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

omit [Fintype ν] in
theorem qmaSelectedIndex_mem (s : Finset ν) (i : Fin s.card) : qmaSelectedIndex s i ∈ s :=
  (s.equivFin.symm i).property

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathSchedule
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

namespace QMAPathSchedule

def nextWork (W : QMAPathSchedule) : QMAPartialPathsEdge W.active → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr (i,a)) => if a = 1 then W.work (qmaSelectedIndex W.active i)-1 else 0

def next (W : QMAPathSchedule) (N : ℚ) : QMAPathSchedule where
  graph := W.graph.subdivide W.active (fun _ => false) N
  work := W.nextWork

theorem next_work_le (W : QMAPathSchedule) (N : ℚ) {D : ℕ}
    (hD : ∀ e, W.work e ≤ D) : ∀ e, (W.next N).work e ≤ D-1 := by
  intro e
  rcases e with e | e
  · exact Nat.zero_le _
  rcases e with e | ⟨i,a⟩
  · exact Nat.zero_le _
  change (if a = 1 then W.work (qmaSelectedIndex W.active i)-1 else 0) ≤ D-1
  split
  · exact Nat.sub_le_sub_right (hD _) 1
  · exact Nat.zero_le _

def iterate (W : QMAPathSchedule) (N : ℚ) : ℕ → QMAPathSchedule
  | 0 => W
  | k+1 => (W.iterate N k).next N

theorem iterate_work_le (W : QMAPathSchedule) (N : ℚ) {D : ℕ}
    (hD : ∀ e, W.work e ≤ D) (k : ℕ) : ∀ e, (W.iterate N k).work e ≤ D-k := by
  induction k with
  | zero => exact hD
  | succ k ih =>
    change ∀ e, ((W.iterate N k).next N).work e ≤ D-(k+1)
    intro e
    have h := (W.iterate N k).next_work_le N ih e
    simpa only [Nat.sub_sub,Nat.add_comm 1 k] using h

theorem iterate_complete (W : QMAPathSchedule) (N : ℚ) {D : ℕ}
    (hD : ∀ e, W.work e ≤ D) : ∀ e, (W.iterate N D).work e = 0 := by
  intro e
  have h := W.iterate_work_le N hD D e
  omega

end QMAPathSchedule
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathEmbedding
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

namespace QMAPathEmbedding
variable {W : QMAPathSchedule} {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding W Γ)

theorem selected_work_pos (i : Fin W.active.card) : 0 < W.work (qmaSelectedIndex W.active i) :=
  (W.mem_active _).mp (qmaSelectedIndex_mem W.active i)

theorem freshPosition_ne_old (i : Fin W.active.card) (b : Fin 2) (v : Fin W.graph.n) :
    P.freshPosition i b ≠ P.position v := by
  apply P.avoids
  · omega
  · have h := selected_work_pos (W := W) i
    have hb := b.isLt
    omega

theorem freshPosition_injective : Function.Injective (fun x : Fin W.active.card × Fin 2 =>
    P.freshPosition x.1 x.2) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  change P.point (qmaSelectedIndex W.active i) (a.val+1) =
    P.point (qmaSelectedIndex W.active j) (b.val+1) at h
  have hi := selected_work_pos (W := W) i
  have hj := selected_work_pos (W := W) j
  have ha := a.isLt
  have hb := b.isLt
  have he : qmaSelectedIndex W.active i = qmaSelectedIndex W.active j := by
    by_contra hn
    exact P.disjoint _ _ (a.val+1) (b.val+1) hn (by omega) (by omega) (by omega) h
  have hij : i = j := by
    apply W.active.equivFin.symm.injective
    exact Subtype.ext he
  subst j
  have hab := P.simple (qmaSelectedIndex W.active i) (a.val+1) (b.val+1) (by omega) (by omega) h
  have : a = b := Fin.ext (by omega)
  subst b
  rfl

theorem nextPosition_injective : Function.Injective P.nextPosition := by
  intro x y h
  obtain ⟨x,rfl⟩ := (vertexEquiv W.graph.n W.active.card).surjective x
  obtain ⟨y,rfl⟩ := (vertexEquiv W.graph.n W.active.card).surjective y
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

theorem adjacent_of_complete (h : ∀ e, W.work e = 0) (e : W.graph.Edge) :
    Γ.Adj (P.position (W.graph.left e)) (P.position (W.graph.right e)) := by
  have hs := P.step e 0 (by omega)
  have hl := P.last e
  simp only [h e,Nat.mul_zero,Nat.zero_add] at hl
  simpa only [P.first e,hl] using hs

end QMAPathEmbedding
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathPieces
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each edge of an odd-subdivision round is an explicitly indexed piece of
one previous route. Interior points of distinct pieces cannot coincide. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPathSchedule

def nextParent (W : QMAPathSchedule) : QMAPartialPathsEdge W.active → W.graph.Edge
  | .inl e => e.val
  | .inr (.inl i) => qmaSelectedIndex W.active i
  | .inr (.inr (i,_)) => qmaSelectedIndex W.active i

def nextIndex (W : QMAPathSchedule) (e : QMAPartialPathsEdge W.active) (k : ℕ) : ℕ :=
  match e with
  | .inl _ => k
  | .inr (.inl _) => k+1
  | .inr (.inr (i,a)) => if a = 0 then k else 2*W.work (qmaSelectedIndex W.active i)+1-k

theorem retained_work_zero (W : QMAPathSchedule) (e : {e // e ∉ W.active}) :
    W.work e.val = 0 := by
  have h := e.property
  simp only [mem_active] at h
  omega

theorem selected_work_pos (W : QMAPathSchedule) (i : Fin W.active.card) :
    0 < W.work (qmaSelectedIndex W.active i) :=
  (W.mem_active _).mp (qmaSelectedIndex_mem W.active i)

theorem nextIndex_bounds (W : QMAPathSchedule) (e : QMAPartialPathsEdge W.active) {k : ℕ}
    (hk : k ≤ 2*W.nextWork e+1) : W.nextIndex e k ≤ 2*W.work (W.nextParent e)+1 := by
  rcases e with e | (i | ⟨i,a⟩)
  · simpa only [nextIndex,nextParent,nextWork,W.retained_work_zero e,Nat.mul_zero,
      Nat.zero_add] using hk
  · have hp := W.selected_work_pos i
    simp only [nextIndex,nextParent,nextWork,Nat.mul_zero,Nat.zero_add] at *
    omega
  · have hp := W.selected_work_pos i
    fin_cases a <;> simp [nextIndex,nextParent,nextWork] at *
    omega

theorem nextIndex_injective (W : QMAPathSchedule) (e : QMAPartialPathsEdge W.active) {i j : ℕ}
    (hi : i ≤ 2*W.nextWork e+1) (hj : j ≤ 2*W.nextWork e+1)
    (h : W.nextIndex e i = W.nextIndex e j) : i = j := by
  rcases e with e | (a | ⟨a,b⟩)
  · exact h
  · simpa only [nextIndex,Nat.add_right_cancel_iff] using h
  · have hp := W.selected_work_pos a
    fin_cases b <;> simp [nextIndex,nextWork] at * <;> omega

theorem nextIndex_interior (W : QMAPathSchedule) (e : QMAPartialPathsEdge W.active) {i : ℕ}
    (hi0 : 0 < i) (hi : i < 2*W.nextWork e+1) :
    2 < W.nextIndex e i ∧ W.nextIndex e i < 2*W.work (W.nextParent e)+1 := by
  rcases e with e | (a | ⟨a,b⟩)
  · simp only [nextWork,Nat.mul_zero,Nat.zero_add] at hi
    omega
  · simp only [nextWork,Nat.mul_zero,Nat.zero_add] at hi
    omega
  · have hp := W.selected_work_pos a
    fin_cases b <;> simp [nextIndex,nextParent,nextWork] at * <;> omega

theorem nextIndex_step (W : QMAPathSchedule) (e : QMAPartialPathsEdge W.active) {i : ℕ}
    (hi : i < 2*W.nextWork e+1) :
    W.nextIndex e (i+1) = W.nextIndex e i+1 ∨
      W.nextIndex e i = W.nextIndex e (i+1)+1 := by
  rcases e with e | (a | ⟨a,b⟩)
  · exact Or.inl rfl
  · exact Or.inl rfl
  · have hp := W.selected_work_pos a
    fin_cases b <;> simp [nextIndex,nextWork] at *
    omega

theorem selectedIndex_injective (W : QMAPathSchedule) :
    Function.Injective (qmaSelectedIndex W.active) := by
  intro i j h
  apply W.active.equivFin.symm.injective
  exact Subtype.ext h

theorem nextIndex_separated (W : QMAPathSchedule) (e f : QMAPartialPathsEdge W.active)
    {i j : ℕ} (hi0 : 0 < i) (hi : i < 2*W.nextWork e+1)
    (hj : j ≤ 2*W.nextWork f+1) (he : W.nextParent e = W.nextParent f)
    (hp : W.nextIndex e i = W.nextIndex f j) : e = f := by
  have hinner := W.nextIndex_interior e hi0 hi
  rcases e with e | (a | ⟨a,b⟩)
  · simp only [nextWork,Nat.mul_zero,Nat.zero_add] at hi
    omega
  · simp only [nextWork,Nat.mul_zero,Nat.zero_add] at hi
    omega
  · fin_cases b
    · simp [nextWork] at hi
      omega
    rcases f with f | (c | ⟨c,d⟩)
    · have hret := W.retained_work_zero f
      have hpos := W.selected_work_pos a
      change qmaSelectedIndex W.active a = f.val at he
      rw [he,hret] at hpos
      omega
    · change qmaSelectedIndex W.active a = qmaSelectedIndex W.active c at he
      have hac := W.selectedIndex_injective he
      subst c
      simp [nextIndex,nextWork] at hj hp
      simp [nextIndex] at hinner
      omega
    · change qmaSelectedIndex W.active a = qmaSelectedIndex W.active c at he
      have hac := W.selectedIndex_injective he
      subst c
      fin_cases d
      · simp [nextIndex,nextWork] at hj hp
        simp [nextIndex] at hinner
        omega
      · rfl

end QMAPathSchedule
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathPlacement
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical placements are preserved by every scheduled odd subdivision. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAPathEmbedding
variable {W : QMAPathSchedule} {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding W Γ)

def nextPoint (e : QMAPartialPathsEdge W.active) (k : ℕ) : ℕ × ℕ :=
  P.point (W.nextParent e) (W.nextIndex e k)

theorem nextPoint_first (e : QMAPartialPathsEdge W.active) :
    P.nextPoint e 0 = P.nextPosition (qmaPartialPathsLeft W.graph.left W.graph.right W.active e) := by
  rcases e with e | (i | ⟨i,a⟩)
  · simpa [nextPoint,QMAPathSchedule.nextParent,QMAPathSchedule.nextIndex,qmaPartialPathsLeft,
      qmaParallelGraphLeft] using P.first e.val
  · simp [nextPoint,QMAPathSchedule.nextParent,QMAPathSchedule.nextIndex,qmaPartialPathsLeft,
      qmaParallelGraphLeft,freshPosition]
  · fin_cases a
    · simpa [nextPoint,QMAPathSchedule.nextParent,QMAPathSchedule.nextIndex,qmaPartialPathsLeft,
        qmaParallelGraphLeft,qmaSelectedSite] using P.first (qmaSelectedIndex W.active i)
    · simpa [nextPoint,QMAPathSchedule.nextParent,QMAPathSchedule.nextIndex,qmaPartialPathsLeft,
        qmaParallelGraphLeft,qmaSelectedSite] using P.last (qmaSelectedIndex W.active i)

theorem nextPoint_last (e : QMAPartialPathsEdge W.active) :
    P.nextPoint e (2*W.nextWork e+1) =
      P.nextPosition (qmaPartialPathsRight W.graph.right W.active (fun _ => false) e) := by
  rcases e with e | (i | ⟨i,a⟩)
  · have hz := W.retained_work_zero e
    simpa [nextPoint,QMAPathSchedule.nextParent,QMAPathSchedule.nextIndex,QMAPathSchedule.nextWork,
      qmaPartialPathsRight,qmaParallelGraphRight,hz] using P.last e.val
  · simp [nextPoint,QMAPathSchedule.nextParent,QMAPathSchedule.nextIndex,QMAPathSchedule.nextWork,
      qmaPartialPathsRight,qmaParallelGraphRight,freshPosition]
  · have hw := W.selected_work_pos i
    fin_cases a
    · simp [nextPoint,QMAPathSchedule.nextParent,QMAPathSchedule.nextIndex,QMAPathSchedule.nextWork,
        qmaPartialPathsRight,qmaParallelGraphRight,qmaPathMember,freshPosition]
    · have hi : 2*W.work (qmaSelectedIndex W.active i)+1 -
          (2*(W.work (qmaSelectedIndex W.active i)-1)+1) = 2 := by omega
      simp [nextPoint,QMAPathSchedule.nextParent,QMAPathSchedule.nextIndex,QMAPathSchedule.nextWork,
        qmaPartialPathsRight,qmaParallelGraphRight,qmaPathMember,freshPosition,hi]

theorem nextPoint_simple (e : QMAPartialPathsEdge W.active) (i j : ℕ)
    (hi : i ≤ 2*W.nextWork e+1) (hj : j ≤ 2*W.nextWork e+1)
    (h : P.nextPoint e i = P.nextPoint e j) : i = j := by
  have he := P.simple _ _ _ (W.nextIndex_bounds e hi) (W.nextIndex_bounds e hj) h
  exact W.nextIndex_injective e hi hj he

theorem nextPoint_step (e : QMAPartialPathsEdge W.active) (i : ℕ)
    (hi : i < 2*W.nextWork e+1) : Γ.Adj (P.nextPoint e i) (P.nextPoint e (i+1)) := by
  have hb := W.nextIndex_bounds e (Nat.le_of_lt hi)
  have hn := W.nextIndex_bounds e (k := i+1) (Nat.succ_le_iff.mpr hi)
  rcases W.nextIndex_step e hi with h | h
  · have hk : W.nextIndex e i < 2*W.work (W.nextParent e)+1 := by omega
    simpa only [nextPoint,h] using P.step (W.nextParent e) (W.nextIndex e i) hk
  · have hk : W.nextIndex e (i+1) < 2*W.work (W.nextParent e)+1 := by omega
    simpa only [nextPoint,h] using (P.step (W.nextParent e) (W.nextIndex e (i+1)) hk).symm

theorem nextPoint_avoids (e : QMAPartialPathsEdge W.active) (i : ℕ)
    (v : Fin (W.graph.n+W.active.card*2)) (hi0 : 0 < i) (hi : i < 2*W.nextWork e+1) :
    P.nextPoint e i ≠ P.nextPosition v := by
  obtain ⟨v,rfl⟩ := (vertexEquiv W.graph.n W.active.card).surjective v
  obtain ⟨hlo,hhi⟩ := W.nextIndex_interior e hi0 hi
  rcases v with v | ⟨a,b⟩
  · change P.point (W.nextParent e) (W.nextIndex e i) ≠ P.nextPosition (old _ _ v)
    rw [nextPosition_old]
    exact P.avoids _ _ v (by omega) hhi
  · simp only [show vertexEquiv W.graph.n W.active.card (Sum.inr (a,b)) = fresh _ _ a b from rfl,
      nextPosition_fresh,freshPosition,nextPoint]
    intro h
    have hp := W.selected_work_pos a
    have hb := b.isLt
    by_cases he : W.nextParent e = qmaSelectedIndex W.active a
    · have hi' : W.nextIndex e i ≤ 2*W.work (qmaSelectedIndex W.active a)+1 := by
        rw [← he]
        omega
      have hj' : b.val+1 ≤ 2*W.work (qmaSelectedIndex W.active a)+1 := by omega
      rw [he] at h
      have hx := P.simple _ _ _ hi' hj' h
      omega
    · exact P.disjoint _ _ _ _ he (by omega) hhi (by omega) h

theorem nextPoint_disjoint (e f : QMAPartialPathsEdge W.active) (i j : ℕ)
    (hef : e ≠ f) (hi0 : 0 < i) (hi : i < 2*W.nextWork e+1) (hj : j ≤ 2*W.nextWork f+1) :
    P.nextPoint e i ≠ P.nextPoint f j := by
  intro h
  obtain ⟨hlo,hhi⟩ := W.nextIndex_interior e hi0 hi
  have hbj := W.nextIndex_bounds f hj
  have he : W.nextParent e = W.nextParent f := by
    by_contra hn
    exact P.disjoint _ _ _ _ hn (by omega) hhi hbj h
  have hbi := W.nextIndex_bounds e (Nat.le_of_lt hi)
  change P.point (W.nextParent e) (W.nextIndex e i) =
    P.point (W.nextParent f) (W.nextIndex f j) at h
  rw [← he] at h hbj
  have hx := P.simple _ _ _ hbi hbj h
  exact hef (W.nextIndex_separated e f hi0 hi hj he hx)

def next (N : ℚ) : QMAPathEmbedding (W.next N) Γ where
  position := P.nextPosition
  position_injective := P.nextPosition_injective
  point := P.nextPoint
  first := P.nextPoint_first
  last := P.nextPoint_last
  simple := P.nextPoint_simple
  step := P.nextPoint_step
  avoids := P.nextPoint_avoids
  disjoint := P.nextPoint_disjoint

end QMAPathEmbedding
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutedSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete odd-route realization with the actual rational Hamiltonian,
finite rectangle, degree bound and accumulated full-space spectral error. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAPathEmbedding
variable {W : QMAPathSchedule} {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding W Γ)

def Bounded (X Y : ℕ) : Prop :=
  (∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y) ∧
    ∀ e k, k ≤ 2*W.work e+1 → (P.point e k).1 < X ∧ (P.point e k).2 < Y

def iterate (P : QMAPathEmbedding W Γ) (N : ℚ) : (k : ℕ) → QMAPathEmbedding (W.iterate N k) Γ
  | 0 => P
  | k+1 => (iterate P N k).next N

end QMAPathEmbedding
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortRouteData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coarse paths may meet in cells, but disjoint grid edges give disjoint port chains. -/

noncomputable section
namespace ContinuumCoulomb

structure QMAPortRouteData (G : QMARationalExchangeGraph) where
  length : G.Edge → ℕ
  length_pos : ∀ e, 0 < length e
  position : Fin G.n → ℕ × ℕ
  position_injective : Function.Injective position
  point : G.Edge → ℕ → ℕ × ℕ
  first : ∀ e, point e 0 = position (G.left e)
  last : ∀ e, point e (length e) = position (G.right e)
  simple : ∀ e i j, i ≤ length e → j ≤ length e → point e i = point e j → i = j
  step : ∀ e i, i < length e → qmaSquareGrid.Adj (point e i) (point e (i+1))
  positive : ∀ e i, i ≤ length e → 0 < (point e i).1 ∧ 0 < (point e i).2
  edges_disjoint : ∀ e f, e ≠ f → ∀ i j, i < length e → j < length f →
    ¬(point e i = point f j ∧ point e (i+1) = point f (j+1)) ∧
    ¬(point e i = point f (j+1) ∧ point e (i+1) = point f j)

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

abbrev schedule : QMAPathSchedule := ⟨G,P.length⟩

def graph : SimpleGraph (ℕ × ℕ) := SimpleGraph.fromRel (fun x y => ∃ (e : G.Edge) (k : ℕ),
  k < 2*P.length e+1 ∧ qmaPortChain (P.point e) (P.length e) k = x ∧
    qmaPortChain (P.point e) (P.length e) (k+1) = y)

def toEmbedding : QMAPathEmbedding P.schedule P.graph where
  position := fun v => qmaExpandedPoint (P.position v)
  position_injective := qmaExpandedPoint_injective.comp P.position_injective
  point := fun e => qmaPortChain (P.point e) (P.length e)
  first := by intro e; rw [qmaPortChain_zero,P.first]
  last := by intro e; change qmaPortChain (P.point e) (P.length e) (2*P.length e+1) = _
             rw [qmaPortChain_last,P.last]
  simple := by
    intro e i j hi hj h
    exact qmaPortChain_injective _ (P.length_pos e) (P.step e) (P.positive e) (P.simple e) hi hj h
  step := by
    intro e i hi
    change i < 2*P.length e+1 at hi
    apply (SimpleGraph.fromRel_adj _ _ _).mpr
    refine ⟨?_,Or.inl ⟨e,i,hi,rfl,rfl⟩⟩
    intro h
    have he := qmaPortChain_injective _ (P.length_pos e) (P.step e) (P.positive e) (P.simple e)
      (Nat.le_of_lt hi) (by omega) h
    omega
  avoids := by
    intro e i v hi0 hi
    exact qmaPortChain_inner_not_center _ hi0 hi _
  disjoint := by
    intro e f i j hef hi0 hi hj
    exact qmaPortChain_interiors_disjoint _ _ (P.step e) (P.step f) (P.positive e) (P.positive f)
      (P.edges_disjoint e f hef) hi0 hi hj

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCellPassages
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A visit to an internal coarse cell occupies two different directional ports. -/

noncomputable section
namespace ContinuumCoulomb
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

abbrev Interior := Σ e : G.Edge, Fin (P.length e-1)

def cell (i : P.Interior) : ℕ × ℕ := P.point i.1 (i.2.val+1)

def armIndex (i : P.Interior) (a : Fin 2) : ℕ := i.2.val+2*a.val

def arm (i : P.Interior) (a : Fin 2) : ℕ × ℕ := P.point i.1 (P.armIndex i a)

theorem cell_index_lt (i : P.Interior) : i.2.val+1 < P.length i.1 := by
  have hi := i.2.isLt
  omega

theorem armIndex_le (i : P.Interior) (a : Fin 2) : P.armIndex i a ≤ P.length i.1 := by
  have hi := i.2.isLt
  have ha := a.isLt
  dsimp [armIndex]
  omega

theorem arm_adjacent (i : P.Interior) (a : Fin 2) : qmaSquareGrid.Adj (P.cell i) (P.arm i a) := by
  have hi := P.cell_index_lt i
  fin_cases a
  · exact (P.step i.1 i.2.val (by omega)).symm
  · exact P.step i.1 (i.2.val+1) hi

def port (i : P.Interior) (a : Fin 2) : Fin 4 := qmaGridNeighborIndex (P.cell i) (P.arm i a)

theorem port_spec (i : P.Interior) (a : Fin 2) :
    qmaGridNeighbor (P.cell i) (P.port i a) = P.arm i a :=
  qmaGridNeighborIndex_spec (P.positive i.1 _ (P.cell_index_lt i).le).1
    (P.positive i.1 _ (P.cell_index_lt i).le).2 (P.arm_adjacent i a)

theorem port_injective (i : P.Interior) : Function.Injective (P.port i) := by
  intro a b h
  have he := congrArg (qmaGridNeighbor (P.cell i)) h
  rw [P.port_spec,P.port_spec] at he
  have hi := P.simple i.1 (P.armIndex i a) (P.armIndex i b)
    (P.armIndex_le i a) (P.armIndex_le i b) he
  apply Fin.ext
  dsimp [armIndex] at hi
  omega

theorem cell_eq_same_edge {i j : P.Interior} (he : i.1 = j.1) (hc : P.cell i = P.cell j) : i = j := by
  rcases i with ⟨e,i⟩
  rcases j with ⟨f,j⟩
  dsimp only at he
  subst f
  have hi := P.simple e (i.val+1) (j.val+1) (P.cell_index_lt ⟨e,i⟩).le
    (P.cell_index_lt ⟨e,j⟩).le hc
  have hij : i = j := Fin.ext (by omega)
  subst j
  rfl

theorem incidence_injective : Function.Injective
    (fun x : P.Interior × Fin 2 => (P.cell x.1,P.port x.1 x.2)) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have hc : P.cell i = P.cell j := congrArg Prod.fst h
  have hp : P.port i a = P.port j b := congrArg Prod.snd h
  have ha : P.arm i a = P.arm j b := by
    rw [← P.port_spec i a,← P.port_spec j b,hc,hp]
  have hij : i.1 = j.1 := by
    by_contra hef
    have hdis := P.edges_disjoint i.1 j.1 hef
    have hi := P.cell_index_lt i
    have hj := P.cell_index_lt j
    have hib := i.2.isLt
    have hjb := j.2.isLt
    fin_cases a <;> fin_cases b
    · exact (hdis i.2.val j.2.val (by omega) (by omega)).1 ⟨ha,hc⟩
    · exact (hdis i.2.val (j.2.val+1) (by omega) hj).2 ⟨ha,hc⟩
    · exact (hdis (i.2.val+1) j.2.val hi (by omega)).2 ⟨hc,ha⟩
    · exact (hdis (i.2.val+1) (j.2.val+1) hi hj).1 ⟨hc,ha⟩
  have he : i = j := P.cell_eq_same_edge hij hc
  subst j
  have hab : a = b := P.port_injective i hp
  subst b
  rfl

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCellMatching
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Internal visits form a matching on the four ports of each cell. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

abbrev CellVisits (p : ℕ × ℕ) := {i : P.Interior // P.cell i = p}

def cellPort (p : ℕ × ℕ) (x : P.CellVisits p × Fin 2) : Fin 4 := P.port x.1.val x.2

theorem cellPort_injective (p : ℕ × ℕ) : Function.Injective (P.cellPort p) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have he : (i.val,a) = (j.val,b) := P.incidence_injective (Prod.ext (i.property.trans j.property.symm) h)
  have hi : i = j := Subtype.ext (congrArg Prod.fst he)
  have hab : a = b := congrArg Prod.snd he
  exact Prod.ext hi hab

theorem cellVisits_card (p : ℕ × ℕ) : Fintype.card (P.CellVisits p) ≤ 2 := by
  have h := Fintype.card_le_of_injective (P.cellPort p) (P.cellPort_injective p)
  simp only [Fintype.card_prod,Fintype.card_fin] at h
  omega

theorem different_visits_ports {i j : P.Interior} (hij : i ≠ j) (hc : P.cell i = P.cell j)
    (a b : Fin 2) : P.port i a ≠ P.port j b := by
  intro h
  have he : (i,a) = (j,b) := P.incidence_injective (Prod.ext hc h)
  exact hij (congrArg Prod.fst he)

theorem two_visits_port_injective {i j : P.Interior} (hij : i ≠ j) (hc : P.cell i = P.cell j) :
    Function.Injective (![P.port i 0,P.port i 1,P.port j 0,P.port j 1] : Fin 4 → Fin 4) := by
  have hi : P.port i 0 ≠ P.port i 1 := (P.port_injective i).ne (by decide)
  have hj : P.port j 0 ≠ P.port j 1 := (P.port_injective j).ne (by decide)
  have h00 := P.different_visits_ports hij hc 0 0
  have h01 := P.different_visits_ports hij hc 0 1
  have h10 := P.different_visits_ports hij hc 1 0
  have h11 := P.different_visits_ports hij hc 1 1
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all

def twoVisitsEquiv {i j : P.Interior} (hij : i ≠ j) (hc : P.cell i = P.cell j) : Fin 4 ≃ Fin 4 :=
  Equiv.ofBijective ![P.port i 0,P.port i 1,P.port j 0,P.port j 1]
    ⟨P.two_visits_port_injective hij hc,Finite.surjective_of_injective (P.two_visits_port_injective hij hc)⟩

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCellCrossings
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An exact finite set of crossing cells, selected from the route visits. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def pairing (i j : P.Interior) : Finset (Sym2 (Fin 4)) :=
  qmaPortPairing ![P.port i 0,P.port i 1,P.port j 0,P.port j 1]

def IsCrossing (p : ℕ × ℕ) : Prop :=
  ∃ i j : P.Interior, i ≠ j ∧ P.cell i = p ∧ P.cell j = p ∧ P.pairing i j = qmaCrossPortPairing

def crossingCells : Finset (ℕ × ℕ) := (Finset.univ.image P.cell).filter P.IsCrossing

@[simp] theorem mem_crossingCells {p : ℕ × ℕ} : p ∈ P.crossingCells ↔ P.IsCrossing p := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    obtain ⟨i,j,hij,hi,hj,hp⟩ := h
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩,i,j,hij,hi,hj,hp⟩

end QMAPortRouteData
end ContinuumCoulomb

end

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

theorem qmaCellPair_complete (a b : Fin 4) (hab : a ≠ b) :
    ∃ e : Fin 6, (a = qmaCellPairLeft e ∧ b = qmaCellPairRight e) ∨
      (a = qmaCellPairRight e ∧ b = qmaCellPairLeft e) := by
  fin_cases a <;> fin_cases b <;> first | exact (hab rfl).elim | decide

theorem qmaCellPair_disjoint (e f : Fin 6)
    (h00 : qmaCellPairLeft e ≠ qmaCellPairLeft f)
    (h01 : qmaCellPairLeft e ≠ qmaCellPairRight f)
    (h10 : qmaCellPairRight e ≠ qmaCellPairLeft f)
    (h11 : qmaCellPairRight e ≠ qmaCellPairRight f)
    (hc : ¬(e = 1 ∧ f = 4) ∧ ¬(e = 4 ∧ f = 1)) :
    Disjoint (qmaCellPairPath e).toFinset (qmaCellPairPath f).toFinset := by
  fin_cases e <;> fin_cases f <;>
    first | exact (h00 rfl).elim | exact (h01 rfl).elim |
      exact (h10 rfl).elim | exact (h11 rfl).elim |
      exact (hc.1 ⟨rfl,rfl⟩).elim | exact (hc.2 ⟨rfl,rfl⟩).elim | decide

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumInnerPorts
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.qmaPointCell_center _root_.OAI.ContinuumCoulomb.qmaPointCell_port _root_.OAI.ContinuumCoulomb.qmaPortChain_last _root_.OAI.ContinuumCoulomb.qmaPortChain_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving crossing terminals one unit into their private patch leaves the
external corridors free and creates space for the two mediator spins. -/

namespace ContinuumCoulomb

theorem qmaInnerPort_cell (p : ℕ × ℕ) (a : Fin 4) :
    ((qmaInnerPort p a).1/32,(qmaInnerPort p a).2/32) = p := by
  apply Prod.ext <;> fin_cases a <;> simp [qmaInnerPort,Nat.add_div]

theorem qmaInnerPort_injective : Function.Injective
    (fun x : (ℕ × ℕ) × Fin 4 => qmaInnerPort x.1 x.2) := by
  rintro ⟨p,a⟩ ⟨q,b⟩ h
  have he := congrArg (fun z : ℕ × ℕ => (z.1/32,z.2/32)) h
  simp only [qmaInnerPort_cell] at he
  subst q
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  have hab : a = b := by fin_cases a <;> fin_cases b <;> simp [qmaInnerPort] at hx hy ⊢
  subst b
  rfl

theorem qmaInnerPort_ne_center (p q : ℕ × ℕ) (a : Fin 4) :
    qmaInnerPort p a ≠ qmaExpandedPoint q := by
  intro h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases a <;> simp [qmaInnerPort,qmaExpandedPoint] at hx hy <;> omega

theorem qmaInnerPort_ne_port (p q : ℕ × ℕ) (a b : Fin 4) :
    qmaInnerPort p a ≠ qmaGridPort q b := by
  intro h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases a <;> fin_cases b <;> simp [qmaInnerPort,qmaGridPort] at hx hy <;> omega

theorem qmaGadgetAncilla_ne_center (p q : ℕ × ℕ) (a : Fin 2) :
    qmaGadgetAncilla p a ≠ qmaExpandedPoint q := by
  intro h
  have hx := congrArg Prod.fst h
  fin_cases a <;> simp [qmaGadgetAncilla,qmaExpandedPoint] at hx <;> omega

theorem qmaGadgetAncilla_ne_port (p q : ℕ × ℕ) (a : Fin 2) (b : Fin 4) :
    qmaGadgetAncilla p a ≠ qmaGridPort q b := by
  intro h
  have hx := congrArg Prod.fst h
  fin_cases a <;> fin_cases b <;> simp [qmaGadgetAncilla,qmaGridPort] at hx <;> omega

theorem qmaGadgetAncilla_ne_inner (p q : ℕ × ℕ) (a : Fin 2) (b : Fin 4) :
    qmaGadgetAncilla p a ≠ qmaInnerPort q b := by
  intro h
  have hx := congrArg Prod.fst h
  fin_cases a <;> fin_cases b <;> simp [qmaGadgetAncilla,qmaInnerPort] at hx <;> omega

theorem qmaPortIndex_spec (p : ℕ × ℕ) (a : Fin 4) : qmaPortIndex (qmaGridPort p a) = a := by
  fin_cases a <;> simp [qmaPortIndex,qmaGridPort,Nat.add_mod]

def qmaCrossingMove (cross : (ℕ × ℕ) → Prop) [DecidablePred cross] (z : ℕ × ℕ) : ℕ × ℕ :=
  let p := (z.1/32,z.2/32)
  if cross p ∧ z ≠ qmaExpandedPoint p then qmaInnerPort p (qmaPortIndex z) else z

theorem qmaCrossingMove_center (cross : (ℕ × ℕ) → Prop) [DecidablePred cross] (p : ℕ × ℕ) :
    qmaCrossingMove cross (qmaExpandedPoint p) = qmaExpandedPoint p := by
  simp [qmaCrossingMove,qmaExpandedPoint_cell]

theorem qmaCrossingMove_port (cross : (ℕ × ℕ) → Prop) [DecidablePred cross] (p : ℕ × ℕ) (a : Fin 4) :
    qmaCrossingMove cross (qmaGridPort p a) = if cross p then qmaInnerPort p a else qmaGridPort p a := by
  simp only [qmaCrossingMove,qmaGridPort_cell,qmaPortIndex_spec]
  by_cases hp : cross p
  · rw [ite_eq_left ⟨hp,qmaGridPort_ne_center p p a⟩,ite_eq_left hp]
  · rw [ite_eq_right (fun h => hp h.1),ite_eq_right hp]

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

theorem qmaHalfCorridor_disjoint (cross : Bool) (a b : Fin 4) (hab : a ≠ b) :
    Disjoint (qmaHalfCorridorPath cross a).toFinset (qmaHalfCorridorPath cross b).toFinset := by
  cases cross <;> fin_cases a <;> fin_cases b <;> first | exact (hab rfl).elim | decide

theorem qmaHalfCorridor_pair (a : Fin 4) (e : Fin 6) :
    Disjoint ((qmaHalfCorridorPath false a).drop 1).toFinset (qmaCellPairPath e).toFinset := by
  fin_cases a <;> fin_cases e <;> decide

theorem qmaHalfCorridor_ray (a b : Fin 4) :
    Disjoint ((qmaHalfCorridorPath false a).drop 1).toFinset (qmaCellRayPath b).toFinset := by
  fin_cases a <;> fin_cases b <;> decide

theorem qmaHalfCorridor_patch (a : Fin 4) (e : Fin 9) :
    Disjoint ((qmaHalfCorridorPath true a).drop 1).toFinset (qmaLocalPatchPath e).toFinset := by
  fin_cases a <;> fin_cases e <;> decide

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCellTranslate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cell-local paths translate injectively and different cells are disjoint. -/

namespace ContinuumCoulomb

theorem qmaCellTranslate_inner (p : ℕ × ℕ) (a : Fin 4) :
    qmaCellTranslate p (qmaInnerPort (0,0) a) = qmaInnerPort p a := by
  fin_cases a <;> rfl

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortLinks
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every port-chain interaction is a vertex ray, a pairing inside one cell,
or the single corridor joining opposite ports of adjacent cells. -/

namespace ContinuumCoulomb

def QMAPortLink (x y : ℕ × ℕ) : Prop :=
  (∃ p a, (x = qmaExpandedPoint p ∧ y = qmaGridPort p a) ∨
    (x = qmaGridPort p a ∧ y = qmaExpandedPoint p)) ∨
  (∃ p a b, x = qmaGridPort p a ∧ y = qmaGridPort p b) ∨
  (∃ p q, qmaSquareGrid.Adj p q ∧ x = qmaDirectedPort p q ∧ y = qmaDirectedPort q p)

theorem QMAPortLink.symm {x y : ℕ × ℕ} (h : QMAPortLink x y) : QMAPortLink y x := by
  rcases h with ⟨p,a,h | h⟩ | ⟨p,a,b,hx,hy⟩ | ⟨p,q,ha,hx,hy⟩
  · exact Or.inl ⟨p,a,Or.inr ⟨h.2,h.1⟩⟩
  · exact Or.inl ⟨p,a,Or.inl ⟨h.2,h.1⟩⟩
  · exact Or.inr (Or.inl ⟨p,b,a,hy,hx⟩)
  · exact Or.inr (Or.inr ⟨q,p,ha.symm,hy,hx⟩)

theorem qmaRoutePort_even (p : ℕ → ℕ × ℕ) (k : ℕ) :
    qmaRoutePort p (2*k) = qmaDirectedPort (p k) (p (k-1)) := by
  simp [qmaRoutePort,qmaPortNeighborIndex]

theorem qmaRoutePort_odd (p : ℕ → ℕ × ℕ) (k : ℕ) :
    qmaRoutePort p (2*k+1) = qmaDirectedPort (p k) (p (k+1)) := by
  simp [qmaRoutePort,qmaPortNeighborIndex,Nat.add_div]

theorem qmaPortChain_link (p : ℕ → ℕ × ℕ) {L : ℕ} (hL : 0 < L)
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1)))
    (i : ℕ) (hi : i < 2*L+1) : QMAPortLink (qmaPortChain p L i) (qmaPortChain p L (i+1)) := by
  by_cases hi0 : i = 0
  · subst i
    rw [qmaPortChain_zero,qmaPortChain_inner p (by omega : 0 < 0+1) (by omega : 0+1 < 2*L+1)]
    have he := qmaRoutePort_odd p 0
    simp only [Nat.mul_zero,Nat.zero_add] at he
    rw [he]
    exact Or.inl ⟨p 0,qmaGridNeighborIndex (p 0) (p 1),Or.inl ⟨rfl,rfl⟩⟩
  by_cases hil : i = 2*L
  · subst i
    rw [qmaPortChain_last,qmaPortChain_inner p (by omega : 0 < 2*L) (by omega : 2*L < 2*L+1),
      qmaRoutePort_even]
    exact Or.inl ⟨p L,qmaGridNeighborIndex (p L) (p (L-1)),Or.inr ⟨rfl,rfl⟩⟩
  rw [qmaPortChain_inner p (by omega) hi,qmaPortChain_inner p (by omega : 0 < i+1) (by omega)]
  by_cases ho : i%2 = 1
  · have he : i = 2*(i/2)+1 := by omega
    rw [he,qmaRoutePort_odd]
    have hn : 2*(i/2)+1+1 = 2*(i/2+1) := by omega
    rw [hn,qmaRoutePort_even,Nat.add_sub_cancel]
    exact Or.inr (Or.inr ⟨p (i/2),p (i/2+1),hp _ (by omega),rfl,rfl⟩)
  · have he : i = 2*(i/2) := by omega
    rw [he,qmaRoutePort_even,qmaRoutePort_odd]
    exact Or.inr (Or.inl ⟨p (i/2),qmaGridNeighborIndex (p (i/2)) (p (i/2-1)),
      qmaGridNeighborIndex (p (i/2)) (p (i/2+1)),rfl,rfl⟩)

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortInnerPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A port-chain edge with both ends in the same cell is precisely one internal
route visit, with the incoming and outgoing directions in order. -/

namespace ContinuumCoulomb

theorem qmaPortChain_inner_pair (p : ℕ → ℕ × ℕ) {L k : ℕ}
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1)))
    (hk : k < 2*L+1) (q : ℕ × ℕ) (a b : Fin 4)
    (hl : qmaPortChain p L k = qmaGridPort q a)
    (hr : qmaPortChain p L (k+1) = qmaGridPort q b) :
    ∃ t, 0 < t ∧ t < L ∧ p t = q ∧
      qmaGridNeighborIndex (p t) (p (t-1)) = a ∧ qmaGridNeighborIndex (p t) (p (t+1)) = b := by
  have hk0 : 0 < k := by
    by_contra hn
    have he : k = 0 := by omega
    subst k
    rw [qmaPortChain_zero] at hl
    exact qmaGridPort_ne_center q (p 0) a hl.symm
  have hkl : k+1 < 2*L+1 := by
    by_contra hn
    have he : k+1 = 2*L+1 := by omega
    rw [he,qmaPortChain_last] at hr
    exact qmaGridPort_ne_center q (p L) b hr.symm
  rw [qmaPortChain_inner p hk0 hk] at hl
  rw [qmaPortChain_inner p (by omega) hkl] at hr
  by_cases ho : k%2 = 1
  · have he : k = 2*(k/2)+1 := by omega
    rw [he,qmaRoutePort_odd] at hl
    have he' : k+1 = 2*(k/2+1) := by omega
    rw [he',qmaRoutePort_even,Nat.add_sub_cancel] at hr
    have h1 : (p (k/2),qmaGridNeighborIndex (p (k/2)) (p (k/2+1))) = (q,a) :=
      qmaGridPort_injective hl
    have h2 : (p (k/2+1),qmaGridNeighborIndex (p (k/2+1)) (p (k/2))) = (q,b) :=
      qmaGridPort_injective hr
    have heq : p (k/2) = p (k/2+1) := (congrArg Prod.fst h1).trans (congrArg Prod.fst h2).symm
    exact ((hp (k/2) (by omega)).ne heq).elim
  · have he : k = 2*(k/2) := by omega
    rw [he,qmaRoutePort_even] at hl
    rw [he,qmaRoutePort_odd] at hr
    have h1 : (p (k/2),qmaGridNeighborIndex (p (k/2)) (p (k/2-1))) = (q,a) :=
      qmaGridPort_injective hl
    have h2 : (p (k/2),qmaGridNeighborIndex (p (k/2)) (p (k/2+1))) = (q,b) :=
      qmaGridPort_injective hr
    exact ⟨k/2,by omega,by omega,congrArg Prod.fst h1,congrArg Prod.snd h1,congrArg Prod.snd h2⟩

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortGraphPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Edges wholly inside one port cell are exactly the two ports of a route visit. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem visit_of_forward_pair (e : G.Edge) (k : ℕ) (hk : k < 2*P.length e+1)
    (p : ℕ × ℕ) (a b : Fin 4)
    (hl : qmaPortChain (P.point e) (P.length e) k = qmaGridPort p a)
    (hr : qmaPortChain (P.point e) (P.length e) (k+1) = qmaGridPort p b) :
    ∃ i : P.Interior, P.cell i = p ∧ P.port i 0 = a ∧ P.port i 1 = b := by
  obtain ⟨t,ht0,ht,hp,ha,hb⟩ := qmaPortChain_inner_pair (P.point e) (P.step e) hk p a b hl hr
  let i : P.Interior := ⟨e,⟨t-1,by omega⟩⟩
  have h1 : t-1+1 = t := by omega
  have h2 : t-1+2*1 = t+1 := by omega
  refine ⟨i,?_,?_,?_⟩
  · simpa only [cell,i,h1] using hp
  · simpa only [port,cell,arm,armIndex,i,Fin.val_zero,Nat.mul_zero,Nat.add_zero,h1] using ha
  · simpa only [port,cell,arm,armIndex,i,Fin.val_one,h1,h2] using hb

theorem graph_inner_pair {p : ℕ × ℕ} {a b : Fin 4}
    (h : P.graph.Adj (qmaGridPort p a) (qmaGridPort p b)) :
    ∃ i : P.Interior, P.cell i = p ∧
      ((P.port i 0 = a ∧ P.port i 1 = b) ∨ (P.port i 0 = b ∧ P.port i 1 = a)) := by
  change _ ≠ _ ∧ _ at h
  rcases h.2 with ⟨e,k,hk,hl,hr⟩ | ⟨e,k,hk,hl,hr⟩
  · obtain ⟨i,hi,ha,hb⟩ := P.visit_of_forward_pair e k hk p a b hl hr
    exact ⟨i,hi,Or.inl ⟨ha,hb⟩⟩
  · obtain ⟨i,hi,hb,ha⟩ := P.visit_of_forward_pair e k hk p b a hl hr
    exact ⟨i,hi,Or.inr ⟨hb,ha⟩⟩

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingPairSupport
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At a selected crossing, every internal port edge is one of its two opposite
pairs. This excludes leftover crossed interactions after edge selection. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem cell_visits_third {p : ℕ × ℕ} {i j k : P.Interior} (hij : i ≠ j)
    (hi : P.cell i = p) (hj : P.cell j = p) (hk : P.cell k = p) : k = i ∨ k = j := by
  by_contra hn
  push Not at hn
  let a : P.CellVisits p := ⟨i,hi⟩
  let b : P.CellVisits p := ⟨j,hj⟩
  let c : P.CellVisits p := ⟨k,hk⟩
  have hab : a ≠ b := fun h => hij (congrArg Subtype.val h)
  have hca : c ≠ a := fun h => hn.1 (congrArg Subtype.val h)
  have hcb : c ≠ b := fun h => hn.2 (congrArg Subtype.val h)
  have hs : ({a,b,c} : Finset (P.CellVisits p)).card = 3 := by simp [hab,hca.symm,hcb.symm]
  have hc := Finset.card_le_univ ({a,b,c} : Finset (P.CellVisits p))
  have hp := P.cellVisits_card p
  omega

theorem crossing_graph_pair {p : ℕ × ℕ} (hp : P.IsCrossing p) {a b : Fin 4}
    (h : P.graph.Adj (qmaGridPort p a) (qmaGridPort p b)) : s(a,b) ∈ qmaCrossPortPairing := by
  obtain ⟨i,j,hij,hi,hj,hpair⟩ := hp
  obtain ⟨k,hk,hab⟩ := P.graph_inner_pair h
  have hki := P.cell_visits_third hij hi hj hk
  rw [← hpair]
  change s(a,b) ∈ {s(P.port i 0,P.port i 1),s(P.port j 0,P.port j 1)}
  rcases hki with rfl | rfl
  · rcases hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert.mpr
      exact Or.inl Sym2.eq_swap
  · rcases hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_singleton.mpr Sym2.eq_swap

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRationalCrossing
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

structure QMARationalCrossingLayer (r : ℕ) where
  base : QMARationalExchangeGraph
  site : Fin r → Fin 4 → Fin base.n
  injective : ∀ i, Function.Injective (site i)
  J : Fin r → ℚ
  K : Fin r → ℚ

namespace QMARationalCrossingLayer
variable {r : ℕ}

def scale (C : QMARationalCrossingLayer r) (N : ℚ) : ℚ :=
  let B := 3*(∑ e, |C.base.weight e|)+|C.base.constant|
  let A := 6*∑ i, (1+|C.J i|+|C.K i|)
  let D := B+12*∑ i, (1+|C.J i|+|C.K i|)^2
  16*(A+D+1)^3*N+4*(A+D+1)+1

def output (C : QMARationalCrossingLayer r) (N : ℚ) : QMARationalExchangeGraph where
  n := C.base.n+r*2
  Edge := QMACrossingsGraphEdge C.base.Edge r
  left := qmaParallelGraphLeft (qmaCrossingsBaseLeft C.base.left C.site) C.site
  right := qmaParallelGraphRight (qmaCrossingsBaseRight C.base.right C.site) (fun _ => qmaCrossingMember)
  distinct := qmaParallelGraph_distinct _ _
    (qmaCrossingsBase_distinct _ _ C.base.distinct C.site C.injective) _ _
  weight := fun e => match e with
    | .inl (.inl e) => C.base.weight e
    | .inl (.inr (i,a)) => QuantumRoutingCode.coefficients (C.scale N,C.J i,C.K i) ⟨a.val+5,by omega⟩
    | .inr (.inl _) => (C.scale N)^2
    | .inr (.inr (i,a)) => QuantumRoutingCode.coefficients (C.scale N,C.J i,C.K i) ⟨a.val+1,by omega⟩
  constant := (C.base.constant+∑ i, (3/2+3*(C.J i)^2+3*(C.K i)^2))+3*(r:ℚ)*(C.scale N)^2

end QMARationalCrossingLayer
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Group a selected family of physical crossing edges without assuming a matrix
identity. Each source edge is either retained or assigned to one crossing pair. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

structure QMARationalCrossingSelection (G : QMARationalExchangeGraph) (r : ℕ) where
  site : Fin r → Fin 4 → Fin G.n
  injective : ∀ i, Function.Injective (site i)
  tag : G.Edge → Option (Fin r × Fin 2)
  tagged : ∀ e i a, tag e = some (i,a) →
    (G.left e = site i (if a = 0 then 0 else 1) ∧ G.right e = site i (if a = 0 then 2 else 3)) ∨
    (G.left e = site i (if a = 0 then 2 else 3) ∧ G.right e = site i (if a = 0 then 0 else 1))

namespace QMARationalCrossingSelection
variable {G : QMARationalExchangeGraph} {r : ℕ} (S : QMARationalCrossingSelection G r)

abbrev retained : QMARationalExchangeGraph where
  n := G.n
  Edge := {e : G.Edge // S.tag e = none}
  left := fun e => G.left e.val
  right := fun e => G.right e.val
  distinct := fun e => G.distinct e.val
  weight := fun e => G.weight e.val
  constant := G.constant

def weight (p : Fin r × Fin 2) : ℚ := ∑ e : {e // S.tag e = some p}, G.weight e.val

def layer : QMARationalCrossingLayer r where
  base := S.retained
  site := S.site
  injective := S.injective
  J := fun i => S.weight (i,0)
  K := fun i => S.weight (i,1)

end QMARationalCrossingSelection
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSelectFromSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The crossing selector is constructed from physical terminal indices. Every
unselected edge avoids every selected pair; no matrix identity is assumed. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMARationalExchangeGraph
variable (G : QMARationalExchangeGraph) {r : ℕ} (site : Fin r → Fin 4 → Fin G.n)

def CrossingMatch (e : G.Edge) (p : Fin r × Fin 2) : Prop :=
  (G.left e = site p.1 (if p.2 = 0 then 0 else 1) ∧
    G.right e = site p.1 (if p.2 = 0 then 2 else 3)) ∨
  (G.left e = site p.1 (if p.2 = 0 then 2 else 3) ∧
    G.right e = site p.1 (if p.2 = 0 then 0 else 1))

def crossingTag (e : G.Edge) : Option (Fin r × Fin 2) :=
  if h : ∃ p, G.CrossingMatch site e p then some (Classical.choose h) else none

theorem crossingTag_some {e : G.Edge} {p : Fin r × Fin 2} (he : G.crossingTag site e = some p) :
    G.CrossingMatch site e p := by
  unfold crossingTag at he
  split_ifs at he with h
  have hp : Classical.choose h = p := Option.some.inj he
  exact hp ▸ Classical.choose_spec h

theorem crossingTag_none {e : G.Edge} : G.crossingTag site e = none ↔ ∀ p, ¬G.CrossingMatch site e p := by
  constructor
  · intro h p hp
    unfold crossingTag at h
    split_ifs at h with hx
    exact hx ⟨p,hp⟩
  · intro h
    have hn : ¬∃ p, G.CrossingMatch site e p := by simpa only [not_exists] using h
    simp only [crossingTag,hn,dite_false]

def crossingSelection (hinj : ∀ i, Function.Injective (site i)) : QMARationalCrossingSelection G r where
  site := site
  injective := hinj
  tag := G.crossingTag site
  tagged := fun _ _ _ he => G.crossingTag_some site he

theorem retained_no_crossing (hinj : ∀ i, Function.Injective (site i))
    (e : (G.crossingSelection site hinj).retained.Edge) (p : Fin r × Fin 2) :
    ¬G.CrossingMatch site e.val p :=
  (G.crossingTag_none site).mp e.property p

end QMARationalExchangeGraph
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathCoverage
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.mem_crossingCells _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every prescribed path point becomes an actual spin when subdivision finishes. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAPathEmbedding
variable {W : QMAPathSchedule} {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding W Γ)

theorem next_covers_point (N : ℚ) (e : W.graph.Edge) (k : ℕ) (hk : k ≤ 2*W.work e+1) :
    ∃ (f : (W.next N).graph.Edge) (l : ℕ), l ≤ 2*(W.next N).work f+1 ∧
      (P.next N).point f l = P.point e k := by
  by_cases he : e ∈ W.active
  · let i : Fin W.active.card := W.active.equivFin ⟨e,he⟩
    have hi : qmaSelectedIndex W.active i = e := by simp [qmaSelectedIndex,i]
    have hw : 0 < W.work e := (W.mem_active e).mp he
    by_cases hk1 : k ≤ 1
    · refine ⟨Sum.inr (Sum.inr (i,0)),k,?_,?_⟩
      · exact hk1
      · change P.point (qmaSelectedIndex W.active i) k = _
        rw [hi]
    by_cases hk2 : k = 2
    · subst k
      refine ⟨Sum.inr (Sum.inl i),1,by exact Nat.le_refl 1,?_⟩
      change P.point (qmaSelectedIndex W.active i) (1+1) = _
      rw [hi]
    · refine ⟨Sum.inr (Sum.inr (i,1)),2*W.work e+1-k,?_,?_⟩
      · change 2*W.work e+1-k ≤ 2*(W.work (qmaSelectedIndex W.active i)-1)+1
        rw [hi]
        omega
      · change P.point (qmaSelectedIndex W.active i)
          (2*W.work (qmaSelectedIndex W.active i)+1-(2*W.work e+1-k)) = _
        rw [hi]
        congr 1
        omega
  · refine ⟨Sum.inl ⟨e,he⟩,k,?_,rfl⟩
    have hle : W.work e ≤ 0 := by simpa only [W.mem_active,not_lt] using he
    have hw : W.work e = 0 := Nat.eq_zero_of_le_zero hle
    change k ≤ 1
    simpa only [hw,Nat.mul_zero,Nat.zero_add] using hk

def Occupied (z : ℕ × ℕ) : Prop :=
  (∃ v, P.position v = z) ∨ ∃ e k, k ≤ 2*W.work e+1 ∧ P.point e k = z

theorem next_occupied (N : ℚ) {z : ℕ × ℕ} (hz : P.Occupied z) : (P.next N).Occupied z := by
  rcases hz with ⟨v,hv⟩ | ⟨e,k,hk,hz⟩
  · exact Or.inl ⟨old W.graph.n W.active.card v,(P.nextPosition_old v).trans hv⟩
  · obtain ⟨f,l,hl,he⟩ := P.next_covers_point N e k hk
    exact Or.inr ⟨f,l,hl,he.trans hz⟩

theorem iterate_occupied (N : ℚ) {z : ℕ × ℕ} (hz : P.Occupied z) (k : ℕ) :
    (P.iterate N k).Occupied z := by
  induction k with
  | zero => exact hz
  | succ k ih => exact (P.iterate N k).next_occupied N ih

theorem occupied_complete (h : ∀ e, W.work e = 0) {z : ℕ × ℕ} (hz : P.Occupied z) :
    ∃ v, P.position v = z := by
  rcases hz with hv | ⟨e,k,hk,hz⟩
  · exact hv
  have hk1 : k ≤ 1 := by simpa only [h e,Nat.mul_zero,Nat.zero_add] using hk
  by_cases hk0 : k = 0
  · subst k
    exact ⟨W.graph.left e,(P.first e).symm.trans hz⟩
  · have hk' : k = 1 := by omega
    have hl := P.last e
    simp only [h e,Nat.mul_zero,Nat.zero_add] at hl
    subst k
    exact ⟨W.graph.right e,hl.symm.trans hz⟩

theorem iterate_covers_point (N : ℚ) {D : ℕ} (hD : ∀ e, W.work e ≤ D)
    (e : W.graph.Edge) (k : ℕ) (hk : k ≤ 2*W.work e+1) :
    ∃ v, (P.iterate N D).position v = P.point e k :=
  (P.iterate N D).occupied_complete (W.iterate_complete N hD)
    (P.iterate_occupied N (Or.inr ⟨e,k,hk,rfl⟩) D)

end QMAPathEmbedding
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathCoverageReverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision only introduces spins at prescribed route points. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAPathEmbedding
variable {W : QMAPathSchedule} {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding W Γ)

theorem next_occupied_source (N : ℚ) {z : ℕ × ℕ} (hz : (P.next N).Occupied z) : P.Occupied z := by
  rcases hz with ⟨v,hv⟩ | ⟨e,k,hk,hz⟩
  · obtain ⟨v,rfl⟩ := (vertexEquiv W.graph.n W.active.card).surjective v
    rcases v with v | ⟨i,b⟩
    · change P.nextPosition (old _ _ v) = z at hv
      rw [P.nextPosition_old] at hv
      exact Or.inl ⟨v,hv⟩
    · change P.nextPosition (fresh _ _ i b) = z at hv
      rw [P.nextPosition_fresh] at hv
      have hw := W.selected_work_pos i
      have hb := b.isLt
      exact Or.inr ⟨qmaSelectedIndex W.active i,b.val+1,by omega,hv⟩
  · change P.point (W.nextParent e) (W.nextIndex e k) = z at hz
    exact Or.inr ⟨W.nextParent e,W.nextIndex e k,W.nextIndex_bounds e hk,hz⟩

theorem iterate_occupied_source (N : ℚ) (k : ℕ) {z : ℕ × ℕ}
    (hz : (P.iterate N k).Occupied z) : P.Occupied z := by
  induction k with
  | zero => exact hz
  | succ k ih => exact ih ((P.iterate N k).next_occupied_source N hz)

end QMAPathEmbedding
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortSpinCoverage
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.qmaPointCell_center _root_.OAI.ContinuumCoulomb.qmaPointCell_port _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Final physical spins lie at original centers or ports, and every occupied
internal port is represented by an actual physical spin. -/

noncomputable section
namespace ContinuumCoulomb

theorem qmaPortChain_kind (p : ℕ → ℕ × ℕ) (L k : ℕ) :
    (∃ q, qmaPortChain p L k = qmaExpandedPoint q) ∨
      ∃ q a, qmaPortChain p L k = qmaGridPort q a := by
  by_cases h0 : k = 0
  · subst k
    exact Or.inl ⟨p 0,qmaPortChain_zero p L⟩
  by_cases hL : k = 2*L+1
  · subst k
    exact Or.inl ⟨p L,qmaPortChain_last p L⟩
  · exact Or.inr ⟨p (k/2),qmaGridNeighborIndex (p (k/2)) (p (qmaPortNeighborIndex k)),
      by simp [qmaPortChain,h0,hL,qmaRoutePort,qmaDirectedPort]⟩

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem cell_port_chain (i : P.Interior) (a : Fin 2) :
    qmaPortChain (P.point i.1) (P.length i.1) (2*(i.2.val+1)+a.val) =
      qmaGridPort (P.cell i) (P.port i a) := by
  have hi := P.cell_index_lt i
  have ha := a.isLt
  rw [qmaPortChain_inner _ (by omega) (by omega)]
  fin_cases a
  · simp only [Nat.add_zero,qmaRoutePort_even,Nat.add_sub_cancel]
    rfl
  · rw [qmaRoutePort_odd]
    rfl

theorem iterate_covers_port (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (i : P.Interior) (a : Fin 2) :
    ∃ v, (P.toEmbedding.iterate N D).position v = qmaGridPort (P.cell i) (P.port i a) := by
  have hi := P.cell_index_lt i
  have ha := a.isLt
  have hb : 2*(i.2.val+1)+a.val ≤ 2*P.length i.1+1 := by omega
  obtain ⟨v,hv⟩ := P.toEmbedding.iterate_covers_point N hD i.1 (2*(i.2.val+1)+a.val) hb
  exact ⟨v,hv.trans (P.cell_port_chain i a)⟩

theorem iterate_position_kind (N : ℚ) (D : ℕ) (v : Fin (P.schedule.iterate N D).graph.n) :
    (∃ p, (P.toEmbedding.iterate N D).position v = qmaExpandedPoint p) ∨
      ∃ p a, (P.toEmbedding.iterate N D).position v = qmaGridPort p a := by
  have h := P.toEmbedding.iterate_occupied_source N D (Or.inl ⟨v,rfl⟩)
  rcases h with ⟨w,hw⟩ | ⟨e,k,_,hk⟩
  · exact Or.inl ⟨P.position w,hw.symm⟩
  · rw [← hk]
    exact qmaPortChain_kind (P.point e) (P.length e) k

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every terminal of every selected crossing is an actual spin in the completed
rational port graph. Distinct crossing cells have disjoint terminal sets. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

abbrev Crossing := {p : ℕ × ℕ // p ∈ P.crossingCells}

abbrev finishedGraph (N : ℚ) (D : ℕ) : QMARationalExchangeGraph := (P.schedule.iterate N D).graph

def finishedPosition (N : ℚ) (D : ℕ) : Fin (P.finishedGraph N D).n → ℕ × ℕ :=
  (P.toEmbedding.iterate N D).position

theorem crossing_terminal_exists (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (c : P.Crossing) (a : Fin 4) :
    ∃ v, P.finishedPosition N D v = qmaGridPort c.val a := by
  obtain ⟨i,j,hij,hi,hj,_⟩ := P.mem_crossingCells.mp c.property
  have hc : P.cell i = P.cell j := hi.trans hj.symm
  obtain ⟨b,hb⟩ := (P.twoVisitsEquiv hij hc).surjective a
  fin_cases b
  · change P.port i 0 = a at hb
    simpa only [finishedPosition,hi,hb] using P.iterate_covers_port N hD i 0
  · change P.port i 1 = a at hb
    simpa only [finishedPosition,hi,hb] using P.iterate_covers_port N hD i 1
  · change P.port j 0 = a at hb
    simpa only [finishedPosition,hj,hb] using P.iterate_covers_port N hD j 0
  · change P.port j 1 = a at hb
    simpa only [finishedPosition,hj,hb] using P.iterate_covers_port N hD j 1

def crossingSite (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) (c : P.Crossing) (a : Fin 4) :
    Fin (P.finishedGraph N D).n := Classical.choose (P.crossing_terminal_exists N hD c a)

theorem crossingSite_spec (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) (c : P.Crossing) (a : Fin 4) :
    P.finishedPosition N D (P.crossingSite N hD c a) = qmaGridPort c.val a :=
  Classical.choose_spec (P.crossing_terminal_exists N hD c a)

theorem crossingSite_injective (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) :
    Function.Injective (fun x : P.Crossing × Fin 4 => P.crossingSite N hD x.1 x.2) := by
  rintro ⟨c,a⟩ ⟨d,b⟩ h
  have hp := congrArg (P.finishedPosition N D) h
  rw [P.crossingSite_spec,P.crossingSite_spec] at hp
  have he : (c.val,a) = (d.val,b) := qmaGridPort_injective hp
  have hcd : c = d := Subtype.ext (congrArg (fun z : (ℕ × ℕ) × Fin 4 => z.1) he)
  have hab : a = b := congrArg (fun z : (ℕ × ℕ) × Fin 4 => z.2) he
  exact Prod.ext hcd hab

end QMAPortRouteData
end ContinuumCoulomb

end

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

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def crossingCell (i : Fin P.crossingCells.card) : P.Crossing := P.crossingCells.equivFin.symm i

def crossingSiteFin (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (i : Fin P.crossingCells.card) (a : Fin 4) : Fin (P.finishedGraph N D).n :=
  P.crossingSite N hD (P.crossingCell i) (qmaPatchDirection a)

theorem crossingSiteFin_injective (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (i : Fin P.crossingCells.card) : Function.Injective (P.crossingSiteFin N hD i) := by
  intro a b h
  have he : (P.crossingCell i,qmaPatchDirection a) = (P.crossingCell i,qmaPatchDirection b) :=
    P.crossingSite_injective N hD h
  exact qmaPatchDirection_injective (congrArg (fun z : P.Crossing × Fin 4 => z.2) he)

def portCrossingSelection (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) :
    QMARationalCrossingSelection (P.finishedGraph N D) P.crossingCells.card :=
  (P.finishedGraph N D).crossingSelection (P.crossingSiteFin N hD) (P.crossingSiteFin_injective N hD)

end QMAPortRouteData
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

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem finished_edge_adjacent (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (e : (P.finishedGraph N D).Edge) :
    P.graph.Adj (P.finishedPosition N D ((P.finishedGraph N D).left e))
      (P.finishedPosition N D ((P.finishedGraph N D).right e)) :=
  (P.toEmbedding.iterate N D).adjacent_of_complete (P.schedule.iterate_complete N hD) e

theorem graph_link {x y : ℕ × ℕ} (h : P.graph.Adj x y) : QMAPortLink x y := by
  change _ ≠ _ ∧ _ at h
  rcases h.2 with ⟨e,k,hk,hl,hr⟩ | ⟨e,k,hk,hl,hr⟩
  · rw [← hl,← hr]
    exact qmaPortChain_link (P.point e) (P.length_pos e) (P.step e) k hk
  · rw [← hl,← hr]
    exact (qmaPortChain_link (P.point e) (P.length_pos e) (P.step e) k hk).symm

theorem finished_edge_link (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (e : (P.finishedGraph N D).Edge) :
    QMAPortLink (P.finishedPosition N D ((P.finishedGraph N D).left e))
      (P.finishedPosition N D ((P.finishedGraph N D).right e)) :=
  P.graph_link (P.finished_edge_adjacent N hD e)

theorem retained_no_internal_crossing (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (e : (P.portCrossingSelection N hD).retained.Edge) (c : P.Crossing) (a b : Fin 4)
    (hl : P.finishedPosition N D ((P.finishedGraph N D).left e.val) = qmaGridPort c.val a)
    (hr : P.finishedPosition N D ((P.finishedGraph N D).right e.val) = qmaGridPort c.val b) : False := by
  have ha := P.finished_edge_adjacent N hD e.val
  rw [hl,hr] at ha
  obtain ⟨t,hab⟩ := qmaCrossPair_direction a b
    (P.crossing_graph_pair (P.mem_crossingCells.mp c.property) ha)
  let i : Fin P.crossingCells.card := P.crossingCells.equivFin c
  have hi : P.crossingCell i = c := P.crossingCells.equivFin.symm_apply_apply c
  have hsite (u : Fin 4) : P.finishedPosition N D (P.crossingSiteFin N hD i u) =
      qmaGridPort c.val (qmaPatchDirection u) := by
    change P.finishedPosition N D (P.crossingSite N hD (P.crossingCell i) _) = _
    rw [hi,P.crossingSite_spec]
  have hinj := (P.toEmbedding.iterate N D).position_injective
  have hvertex (v : Fin (P.finishedGraph N D).n) (u : Fin 4)
      (hv : P.finishedPosition N D v = qmaGridPort c.val (qmaPatchDirection u)) :
      v = P.crossingSiteFin N hD i u := hinj (hv.trans (hsite u).symm)
  apply (P.finishedGraph N D).retained_no_crossing (P.crossingSiteFin N hD)
    (P.crossingSiteFin_injective N hD) e (i,t)
  rcases hab with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact Or.inl ⟨hvertex _ _ (by simpa only [ha] using hl),
      hvertex _ _ (by simpa only [hb] using hr)⟩
  · exact Or.inr ⟨hvertex _ _ (by simpa only [ha] using hl),
      hvertex _ _ (by simpa only [hb] using hr)⟩

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortCellPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every cell touched by an actual port-graph edge lies in the positive quadrant. -/

namespace ContinuumCoulomb

noncomputable section
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem chain_cell_positive (e : G.Edge) (k : ℕ) (hk : k ≤ 2*P.length e+1) :
    0 < (qmaPointCell (qmaPortChain (P.point e) (P.length e) k)).1 ∧
    0 < (qmaPointCell (qmaPortChain (P.point e) (P.length e) k)).2 := by
  by_cases h0 : k = 0
  · subst k
    simpa only [qmaPortChain_zero,qmaPointCell_center] using P.positive e 0 (Nat.zero_le _)
  by_cases hlast : k = 2*P.length e+1
  · subst k
    simpa only [qmaPortChain_last,qmaPointCell_center] using P.positive e (P.length e) le_rfl
  rw [qmaPortChain_inner (P.point e) (by omega) (by omega)]
  change 0 < (qmaPointCell (qmaGridPort (P.point e (k/2)) _)).1 ∧
    0 < (qmaPointCell (qmaGridPort (P.point e (k/2)) _)).2
  rw [qmaPointCell_port]
  exact P.positive e (k/2) (by omega)

theorem graph_cell_positive {x y : ℕ × ℕ} (h : P.graph.Adj x y) :
    (0 < (qmaPointCell x).1 ∧ 0 < (qmaPointCell x).2) ∧
    (0 < (qmaPointCell y).1 ∧ 0 < (qmaPointCell y).2) := by
  change _ ≠ _ ∧ _ at h
  rcases h.2 with ⟨e,k,hk,hl,hr⟩ | ⟨e,k,hk,hl,hr⟩
  · rw [← hl,← hr]
    exact ⟨P.chain_cell_positive e k hk.le,P.chain_cell_positive e (k+1) (by omega)⟩
  · rw [← hl,← hr]
    exact ⟨P.chain_cell_positive e (k+1) (by omega),P.chain_cell_positive e k hk.le⟩

theorem finished_port_cell_positive (N : ℚ) (D : ℕ) (v : Fin (P.finishedGraph N D).n)
    {p : ℕ × ℕ} {a : Fin 4} (hv : P.finishedPosition N D v = qmaGridPort p a) :
    0 < p.1 ∧ 0 < p.2 := by
  have h := P.toEmbedding.iterate_occupied_source N D (Or.inl ⟨v,hv⟩)
  rcases h with ⟨w,hw⟩ | ⟨e,k,hk,he⟩
  · exact (qmaGridPort_ne_center p (P.position w) a hw.symm).elim
  · have hp := P.chain_cell_positive e k hk
    change qmaPortChain (P.point e) (P.length e) k = qmaGridPort p a at he
    simpa only [he,qmaPointCell_port] using hp

end QMAPortRouteData
end
end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRouteEnumeration
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMACellRoute.reverse_body _root_.OAI.ContinuumCoulomb.QMACellRoute.reverse_source _root_.OAI.ContinuumCoulomb.QMACellRoute.reverse_target _root_.OAI.ContinuumCoulomb.QMACellRoute.reverse_valid _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only 140 explicit catalog routes need be tested for a physical edge: the
seventy oriented routes in each endpoint cell. This supplies a fixed finite
search space for the literal planar-route compiler. -/

namespace ContinuumCoulomb

def qmaCellBodies (p : ℕ × ℕ) : List QMACellRouteBody :=
  (List.finRange 4).map (.ray p) ++ (List.finRange 6).map (.pair p) ++
    (List.finRange 9).map (.patch p) ++
      (List.finRange 4).flatMap (fun a =>
        [.corridor p a false false,.corridor p a false true,
         .corridor p a true false,.corridor p a true true])

def qmaCellRoutes (p : ℕ × ℕ) : List QMACellRoute :=
  (qmaCellBodies p).flatMap (fun B => [⟨B,false⟩,⟨B,true⟩])

def qmaRouteCandidates (x y : ℕ × ℕ) : List QMACellRoute :=
  qmaCellRoutes (qmaPointCell x) ++ qmaCellRoutes (qmaPointCell y)

theorem qmaCellBodies_complete (B : QMACellRouteBody) : B ∈ qmaCellBodies B.cell := by
  cases B with
  | ray p a => simp [qmaCellBodies,QMACellRouteBody.cell]
  | pair p a => simp [qmaCellBodies,QMACellRouteBody.cell]
  | patch p a => simp [qmaCellBodies,QMACellRouteBody.cell]
  | corridor p a b c => cases b <;> cases c <;> simp [qmaCellBodies,QMACellRouteBody.cell]

theorem qmaCellRoutes_complete (R : QMACellRoute) : R ∈ qmaCellRoutes R.body.cell := by
  apply List.mem_flatMap.mpr
  refine ⟨R.body,qmaCellBodies_complete R.body,?_⟩
  rcases R with ⟨B,b⟩
  cases b <;> simp

theorem qmaRouteCandidates_complete (R : QMACellRoute) : R ∈ qmaRouteCandidates R.source R.target := by
  have h := qmaCellRoutes_complete R
  have hc : R.body.cell = qmaPointCell R.source ∨ R.body.cell = qmaPointCell R.target := by
    rcases R with ⟨B,b⟩
    cases b
    · exact Or.inl B.source_cell.symm
    · exact Or.inr B.source_cell.symm
  rcases hc with hc | hc
  · apply List.mem_append_left
    rwa [hc] at h
  · apply List.mem_append_right
    rwa [hc] at h

end ContinuumCoulomb

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

abbrev TranslateInput := Pair × Pair

end ContinuumCoulomb.QuantumCellPathProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCellVisitPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual two-port visits choose compatible ordinary-cell paths. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def cellPairIndex (i : P.Interior) : Fin 6 :=
  Classical.choose (qmaCellPair_complete (P.port i 0) (P.port i 1)
    ((P.port_injective i).ne (by decide)))

theorem cellPairIndex_spec (i : P.Interior) :
    (P.port i 0 = qmaCellPairLeft (P.cellPairIndex i) ∧
     P.port i 1 = qmaCellPairRight (P.cellPairIndex i)) ∨
    (P.port i 0 = qmaCellPairRight (P.cellPairIndex i) ∧
     P.port i 1 = qmaCellPairLeft (P.cellPairIndex i)) :=
  Classical.choose_spec (qmaCellPair_complete (P.port i 0) (P.port i 1)
    ((P.port_injective i).ne (by decide)))

theorem cellPairIndex_pair (i : P.Interior) :
    s(qmaCellPairLeft (P.cellPairIndex i),qmaCellPairRight (P.cellPairIndex i)) =
      s(P.port i 0,P.port i 1) := by
  rcases P.cellPairIndex_spec i with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · rw [ha,hb]
  · rw [ha,hb]
    exact Sym2.eq_swap

theorem cellPairIndex_left (i : P.Interior) :
    qmaCellPairLeft (P.cellPairIndex i) = P.port i 0 ∨
      qmaCellPairLeft (P.cellPairIndex i) = P.port i 1 := by
  rcases P.cellPairIndex_spec i with h | h
  · exact Or.inl h.1.symm
  · exact Or.inr h.2.symm

theorem cellPairIndex_right (i : P.Interior) :
    qmaCellPairRight (P.cellPairIndex i) = P.port i 0 ∨
      qmaCellPairRight (P.cellPairIndex i) = P.port i 1 := by
  rcases P.cellPairIndex_spec i with h | h
  · exact Or.inr h.2.symm
  · exact Or.inl h.1.symm

theorem cellPairIndex_non_cross {i j : P.Interior} (hij : i ≠ j)
    (hc : P.cell i = P.cell j) (hn : ¬P.IsCrossing (P.cell i)) :
    ¬(P.cellPairIndex i = 1 ∧ P.cellPairIndex j = 4) ∧
    ¬(P.cellPairIndex i = 4 ∧ P.cellPairIndex j = 1) := by
  have hp : P.pairing i j =
      {s(qmaCellPairLeft (P.cellPairIndex i),qmaCellPairRight (P.cellPairIndex i)),
       s(qmaCellPairLeft (P.cellPairIndex j),qmaCellPairRight (P.cellPairIndex j))} := by
    rw [P.cellPairIndex_pair,P.cellPairIndex_pair]
    rfl
  constructor
  · rintro ⟨hi,hj⟩
    apply hn
    refine ⟨i,j,hij,rfl,hc.symm,?_⟩
    rw [hp,hi,hj]
    rfl
  · rintro ⟨hi,hj⟩
    apply hn
    refine ⟨i,j,hij,rfl,hc.symm,?_⟩
    rw [hp,hi,hj]
    change {s(1,3),s(0,2)} = {s(0,2),s(1,3)}
    exact Finset.pair_comm _ _

theorem ordinary_visit_paths_disjoint {i j : P.Interior} (hij : i ≠ j)
    (hc : P.cell i = P.cell j) (hn : ¬P.IsCrossing (P.cell i)) :
    Disjoint (qmaCellPairPath (P.cellPairIndex i)).toFinset
      (qmaCellPairPath (P.cellPairIndex j)).toFinset := by
  have hne (x y : Fin 4) (hx : x = P.port i 0 ∨ x = P.port i 1)
      (hy : y = P.port j 0 ∨ y = P.port j 1) : x ≠ y := by
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals exact P.different_visits_ports hij hc _ _
  exact qmaCellPair_disjoint _ _
    (hne _ _ (P.cellPairIndex_left i) (P.cellPairIndex_left j))
    (hne _ _ (P.cellPairIndex_left i) (P.cellPairIndex_right j))
    (hne _ _ (P.cellPairIndex_right i) (P.cellPairIndex_left j))
    (hne _ _ (P.cellPairIndex_right i) (P.cellPairIndex_right j))
    (P.cellPairIndex_non_cross hij hc hn)

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingMove
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving only crossing-cell ports is injective on all original spin locations. -/

namespace ContinuumCoulomb

def QMAPortPoint (z : ℕ × ℕ) : Prop :=
  (∃ p, z = qmaExpandedPoint p) ∨ ∃ p a, z = qmaGridPort p a

theorem qmaCrossingMove_injective (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    {x y : ℕ × ℕ} (hx : QMAPortPoint x) (hy : QMAPortPoint y)
    (h : qmaCrossingMove cross x = qmaCrossingMove cross y) : x = y := by
  rcases hx with ⟨p,rfl⟩ | ⟨p,a,rfl⟩ <;> rcases hy with ⟨q,rfl⟩ | ⟨q,b,rfl⟩
  · simpa only [qmaCrossingMove_center] using h
  · simp only [qmaCrossingMove_center,qmaCrossingMove_port] at h
    by_cases hq : cross q
    · rw [ite_eq_left hq] at h
      exact (qmaInnerPort_ne_center q p b h.symm).elim
    · rw [ite_eq_right hq] at h
      exact (qmaGridPort_ne_center q p b h.symm).elim
  · simp only [qmaCrossingMove_center,qmaCrossingMove_port] at h
    by_cases hp : cross p
    · rw [ite_eq_left hp] at h
      exact (qmaInnerPort_ne_center p q a h).elim
    · rw [ite_eq_right hp] at h
      exact (qmaGridPort_ne_center p q a h).elim
  · simp only [qmaCrossingMove_port] at h
    by_cases hp : cross p <;> by_cases hq : cross q
    · rw [ite_eq_left hp,ite_eq_left hq] at h
      have he : (p,a) = (q,b) := qmaInnerPort_injective h
      exact congrArg (fun z : (ℕ × ℕ) × Fin 4 => qmaGridPort z.1 z.2) he
    · rw [ite_eq_left hp,ite_eq_right hq] at h
      exact (qmaInnerPort_ne_port p q a b h).elim
    · rw [ite_eq_right hp,ite_eq_left hq] at h
      exact (qmaInnerPort_ne_port q p b a h.symm).elim
    · simpa only [ite_eq_right hp,ite_eq_right hq] using h

theorem qmaGadgetAncilla_ne_moved (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    (p : ℕ × ℕ) (a : Fin 2) {x : ℕ × ℕ} (hx : QMAPortPoint x) :
    qmaGadgetAncilla p a ≠ qmaCrossingMove cross x := by
  rcases hx with ⟨q,rfl⟩ | ⟨q,b,rfl⟩
  · rw [qmaCrossingMove_center]
    exact qmaGadgetAncilla_ne_center p q a
  · rw [qmaCrossingMove_port]
    split_ifs
    · exact qmaGadgetAncilla_ne_inner p q a b
    · exact qmaGadgetAncilla_ne_port p q a b

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingPlacement
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Injective physical placement for every spin after simultaneous crossing removal. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def movedPosition (N : ℚ) (D : ℕ) (v : Fin (P.finishedGraph N D).n) : ℕ × ℕ :=
  qmaCrossingMove P.IsCrossing (P.finishedPosition N D v)

theorem movedPosition_injective (N : ℚ) (D : ℕ) : Function.Injective (P.movedPosition N D) := by
  intro v w h
  apply (P.toEmbedding.iterate N D).position_injective
  exact qmaCrossingMove_injective P.IsCrossing (P.iterate_position_kind N D v)
    (P.iterate_position_kind N D w) h

theorem movedPosition_site (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) (c : P.Crossing) (a : Fin 4) :
    P.movedPosition N D (P.crossingSite N hD c a) = qmaInnerPort c.val a := by
  unfold movedPosition
  rw [P.crossingSite_spec,qmaCrossingMove_port,ite_eq_left (P.mem_crossingCells.mp c.property)]

def freshCrossingPosition (i : Fin P.crossingCells.card) (b : Fin 2) : ℕ × ℕ :=
  qmaGadgetAncilla (P.crossingCell i).val b

theorem freshCrossingPosition_injective : Function.Injective
    (fun x : Fin P.crossingCells.card × Fin 2 => P.freshCrossingPosition x.1 x.2) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have he : ((P.crossingCell i).val,a) = ((P.crossingCell j).val,b) := qmaGadgetAncilla_injective h
  have hc : P.crossingCell i = P.crossingCell j :=
    Subtype.ext (congrArg (fun z : (ℕ × ℕ) × Fin 2 => z.1) he)
  have hij : i = j := P.crossingCells.equivFin.symm.injective hc
  have hab : a = b := congrArg (fun z : (ℕ × ℕ) × Fin 2 => z.2) he
  exact Prod.ext hij hab

theorem freshCrossingPosition_ne_old (N : ℚ) (D : ℕ) (i : Fin P.crossingCells.card) (a : Fin 2)
    (v : Fin (P.finishedGraph N D).n) : P.freshCrossingPosition i a ≠ P.movedPosition N D v :=
  qmaGadgetAncilla_ne_moved P.IsCrossing (P.crossingCell i).val a (P.iterate_position_kind N D v)

def crossingPosition (N : ℚ) (D : ℕ) :
    Fin ((P.finishedGraph N D).n+P.crossingCells.card*2) → ℕ × ℕ :=
  fun v => Sum.elim (P.movedPosition N D) (fun x => P.freshCrossingPosition x.1 x.2)
    ((vertexEquiv (P.finishedGraph N D).n P.crossingCells.card).symm v)

@[simp] theorem crossingPosition_old (N : ℚ) (D : ℕ) (v : Fin (P.finishedGraph N D).n) :
    P.crossingPosition N D (old _ _ v) = P.movedPosition N D v := by
  simp [crossingPosition,old]

@[simp] theorem crossingPosition_fresh (N : ℚ) (D : ℕ) (i : Fin P.crossingCells.card) (a : Fin 2) :
    P.crossingPosition N D (fresh _ _ i a) = P.freshCrossingPosition i a := by
  simp [crossingPosition,fresh]

theorem crossingPosition_injective (N : ℚ) (D : ℕ) : Function.Injective (P.crossingPosition N D) := by
  intro x y h
  obtain ⟨x,rfl⟩ := (vertexEquiv (P.finishedGraph N D).n P.crossingCells.card).surjective x
  obtain ⟨y,rfl⟩ := (vertexEquiv (P.finishedGraph N D).n P.crossingCells.card).surjective y
  simp only [crossingPosition,Equiv.symm_apply_apply] at h
  apply (vertexEquiv _ _).congr_arg
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (P.movedPosition_injective N D h)
    | inr y => exact (P.freshCrossingPosition_ne_old N D y.1 y.2 x h.symm).elim
  | inr x =>
    cases y with
    | inl y => exact (P.freshCrossingPosition_ne_old N D x.1 x.2 y h).elim
    | inr y => exact congrArg Sum.inr (P.freshCrossingPosition_injective h)

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortRaySupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A center-to-port interaction occurs only at an original source vertex.
Consequently source cells, under the proved no-passage condition, need only rays. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem chain_center_source (e : G.Edge) (k : ℕ) (hk : k ≤ 2*P.length e+1)
    (p : ℕ × ℕ) (hp : qmaPortChain (P.point e) (P.length e) k = qmaExpandedPoint p) :
    ∃ v, P.position v = p := by
  by_cases h0 : k = 0
  · subst k
    rw [qmaPortChain_zero,P.first] at hp
    exact ⟨G.left e,qmaExpandedPoint_injective hp⟩
  by_cases hlast : k = 2*P.length e+1
  · subst k
    rw [qmaPortChain_last,P.last] at hp
    exact ⟨G.right e,qmaExpandedPoint_injective hp⟩
  exact (qmaPortChain_inner_not_center (P.point e) (by omega) (by omega) p hp).elim

theorem graph_center_source {p y : ℕ × ℕ} (h : P.graph.Adj (qmaExpandedPoint p) y) :
    ∃ v, P.position v = p := by
  change _ ≠ _ ∧ _ at h
  rcases h.2 with ⟨e,k,hk,hl,_⟩ | ⟨e,k,hk,_,hr⟩
  · exact P.chain_center_source e k hk.le p hl
  · exact P.chain_center_source e (k+1) (by omega) p hr

theorem finished_center_source (N : ℚ) (D : ℕ) (v : Fin (P.finishedGraph N D).n)
    {p : ℕ × ℕ} (hv : P.finishedPosition N D v = qmaExpandedPoint p) :
    ∃ w, P.position w = p := by
  have h := P.toEmbedding.iterate_occupied_source N D (Or.inl ⟨v,hv⟩)
  rcases h with ⟨w,hw⟩ | ⟨e,k,hk,he⟩
  · exact ⟨w,qmaExpandedPoint_injective hw⟩
  · exact P.chain_center_source e k hk p he

theorem source_not_crossing
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v) (v : Fin G.n) :
    ¬P.IsCrossing (P.position v) := by
  rintro ⟨i,_,_,hi,_,_⟩
  exact havoid i v hi

theorem graph_center_not_crossing
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    {p y : ℕ × ℕ} (h : P.graph.Adj (qmaExpandedPoint p) y) : ¬P.IsCrossing p := by
  obtain ⟨v,rfl⟩ := P.graph_center_source h
  exact P.source_not_crossing havoid v

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRetainedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual retained interactions are source rays, noncrossing cell pairs,
or external corridors. All endpoint positions incorporate the inward move. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaMovedPort (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    (p : ℕ × ℕ) (a : Fin 4) : ℕ × ℕ :=
  if cross p then qmaInnerPort p a else qmaGridPort p a

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def RetainedGeometry (x y : ℕ × ℕ) : Prop :=
  (∃ p a, (∃ v, P.position v = p) ∧ ¬P.IsCrossing p ∧
    ((x = qmaExpandedPoint p ∧ y = qmaGridPort p a) ∨
     (x = qmaGridPort p a ∧ y = qmaExpandedPoint p))) ∨
  (∃ p a b, ¬P.IsCrossing p ∧ x = qmaGridPort p a ∧ y = qmaGridPort p b ∧
    ∃ i : P.Interior, P.cell i = p ∧
      ((P.port i 0 = a ∧ P.port i 1 = b) ∨ (P.port i 0 = b ∧ P.port i 1 = a))) ∨
  (∃ p q, qmaSquareGrid.Adj p q ∧ (0 < p.1 ∧ 0 < p.2) ∧ (0 < q.1 ∧ 0 < q.2) ∧
    x = qmaMovedPort P.IsCrossing p (qmaGridNeighborIndex p q) ∧
    y = qmaMovedPort P.IsCrossing q (qmaGridNeighborIndex q p))

theorem retained_geometry (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.portCrossingSelection N hD).retained.Edge) :
    P.RetainedGeometry
      (P.movedPosition N D ((P.finishedGraph N D).left e.val))
      (P.movedPosition N D ((P.finishedGraph N D).right e.val)) := by
  have hadj := P.finished_edge_adjacent N hD e.val
  rcases P.finished_edge_link N hD e.val with
    ⟨p,a,⟨hl,hr⟩ | ⟨hl,hr⟩⟩ | ⟨p,a,b,hl,hr⟩ | ⟨p,q,hpq,hl,hr⟩
  · have hn : ¬P.IsCrossing p := by
      apply P.graph_center_not_crossing havoid
      simpa only [hl] using hadj
    have hv := P.graph_center_source (by simpa only [hl] using hadj)
    refine Or.inl ⟨p,a,hv,hn,Or.inl ?_⟩
    simp only [movedPosition,hl,hr,qmaCrossingMove_center,qmaCrossingMove_port,hn,ite_false, if_false]
    constructor <;> trivial
  · have hn : ¬P.IsCrossing p := by
      apply P.graph_center_not_crossing havoid
      simpa only [hr] using hadj.symm
    have hv := P.graph_center_source (by simpa only [hr] using hadj.symm)
    refine Or.inl ⟨p,a,hv,hn,Or.inr ?_⟩
    simp only [movedPosition,hl,hr,qmaCrossingMove_center,qmaCrossingMove_port,hn,ite_false, if_false]
    constructor <;> trivial
  · have hn : ¬P.IsCrossing p := by
      intro hc
      exact P.retained_no_internal_crossing N hD e ⟨p,P.mem_crossingCells.mpr hc⟩ a b hl hr
    have hvis := P.graph_inner_pair (by simpa only [hl,hr] using hadj)
    refine Or.inr (Or.inl ⟨p,a,b,hn,?_,?_,hvis⟩)
    · simp only [movedPosition,hl,qmaCrossingMove_port,hn,ite_false, if_false]
    · simp only [movedPosition,hr,qmaCrossingMove_port,hn,ite_false, if_false]
  · have hpos := P.graph_cell_positive hadj
    simp only [hl,hr,qmaDirectedPort,qmaPointCell_port] at hpos
    refine Or.inr (Or.inr ⟨p,q,hpq,hpos.1,hpos.2,?_,?_⟩)
    · simp only [movedPosition,hl,qmaDirectedPort,qmaCrossingMove_port,qmaMovedPort]
    · simp only [movedPosition,hr,qmaDirectedPort,qmaCrossingMove_port,qmaMovedPort]

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRetainedRoutes
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assign an actual short lattice path to every retained physical interaction. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaGridNeighborIndex_opposite {p q : ℕ × ℕ}
    (hp : 0 < p.1 ∧ 0 < p.2) (ha : qmaSquareGrid.Adj p q) :
    qmaGridNeighborIndex q p = qmaPortOpposite (qmaGridNeighborIndex p q) := by
  obtain ⟨a,rfl⟩ := qmaGridNeighbor_exists ha
  rcases p with ⟨x,y⟩
  have hx : x-1+1 = x := by omega
  have hy : y-1+1 = y := by omega
  fin_cases a <;> dsimp [qmaGridNeighborIndex,qmaGridNeighbor,qmaPortOpposite]
  all_goals split_ifs <;> first | rfl | omega

theorem qmaMovedPort_local (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    (p : ℕ × ℕ) (a : Fin 4) :
    qmaMovedPort cross p a = qmaCellTranslate p (qmaLocalPort (decide (cross p)) a) := by
  by_cases h : cross p
  · simp only [qmaMovedPort,qmaLocalPort,h,decide_true,ite_true, if_true,qmaCellTranslate_inner]
  · simp only [qmaMovedPort,qmaLocalPort,h,decide_false,Bool.false_eq_true,ite_false, if_false,qmaCellTranslate_port]

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def RoutingAllowed : QMACellRouteBody → Prop
  | .ray p _ => (∃ v, P.position v = p) ∧ ¬P.IsCrossing p
  | .pair p e => ¬P.IsCrossing p ∧ ∃ i : P.Interior, P.cell i = p ∧
      s(P.port i 0,P.port i 1) = s(qmaCellPairLeft e,qmaCellPairRight e)
  | .patch p _ => P.IsCrossing p
  | .corridor p a b c => b = decide (P.IsCrossing p) ∧
      c = decide (P.IsCrossing (qmaGridNeighbor p a))

theorem geometry_route_exists {x y : ℕ × ℕ} (h : P.RetainedGeometry x y) :
    ∃ R : QMACellRoute, P.RoutingAllowed R.body ∧ R.Valid ∧ R.source = x ∧ R.target = y := by
  rcases h with ⟨p,a,hsource,hn,⟨hx,hy⟩ | ⟨hx,hy⟩⟩ | ⟨p,a,b,hn,hx,hy,i,hi,hv⟩ |
    ⟨p,q,hpq,hp,_,hx,hy⟩
  · exact ⟨⟨.ray p a,false⟩,⟨hsource,hn⟩,trivial,hx.symm,hy.symm⟩
  · exact ⟨⟨.ray p a,true⟩,⟨hsource,hn⟩,trivial,hx.symm,hy.symm⟩
  · have hab : a ≠ b := by
      intro h
      rcases hv with ⟨h0,h1⟩ | ⟨h0,h1⟩
      · exact (by decide : (0 : Fin 2) ≠ 1) (P.port_injective i (h0.trans (h.trans h1.symm)))
      · exact (by decide : (0 : Fin 2) ≠ 1) (P.port_injective i (h0.trans (h.symm.trans h1.symm)))
    have hpair : s(P.port i 0,P.port i 1) = s(a,b) := by
      rcases hv with ⟨h0,h1⟩ | ⟨h0,h1⟩
      · rw [h0,h1]
      · rw [h0,h1]
        exact Sym2.eq_swap
    obtain ⟨e,he⟩ := qmaCellPair_complete a b hab
    rcases he with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · refine ⟨⟨.pair p e,false⟩,⟨hn,i,hi,?_⟩,trivial,?_,?_⟩
      · simpa only [ha,hb] using hpair
      · change qmaGridPort p (qmaCellPairLeft e) = x
        rw [← ha,← hx]
      · change qmaGridPort p (qmaCellPairRight e) = y
        rw [← hb,← hy]
    · refine ⟨⟨.pair p e,true⟩,⟨hn,i,hi,?_⟩,trivial,?_,?_⟩
      · rw [ha,hb] at hpair
        exact hpair.trans Sym2.eq_swap
      · change qmaGridPort p (qmaCellPairRight e) = x
        rw [← ha,← hx]
      · change qmaGridPort p (qmaCellPairLeft e) = y
        rw [← hb,← hy]
  · let a := qmaGridNeighborIndex p q
    refine ⟨⟨.corridor p a (decide (P.IsCrossing p)) (decide (P.IsCrossing q)),false⟩,
      ⟨rfl,?_⟩,hp,?_,?_⟩
    · rw [qmaGridNeighborIndex_spec hp.1 hp.2 hpq]
    · exact (qmaMovedPort_local P.IsCrossing p a).symm.trans hx.symm
    · change qmaCellTranslate (qmaGridNeighbor p a)
        (qmaLocalPort (decide (P.IsCrossing q)) (qmaPortOpposite a)) = y
      rw [qmaGridNeighborIndex_spec hp.1 hp.2 hpq,← qmaGridNeighborIndex_opposite hp hpq]
      exact (qmaMovedPort_local P.IsCrossing q (qmaGridNeighborIndex q p)).symm.trans hy.symm

def retainedRoute (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.portCrossingSelection N hD).retained.Edge) : QMACellRoute :=
  Classical.choose (P.geometry_route_exists (P.retained_geometry N hD havoid e))

theorem retainedRoute_spec (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.portCrossingSelection N hD).retained.Edge) :
    P.RoutingAllowed (P.retainedRoute N hD havoid e).body ∧
    (P.retainedRoute N hD havoid e).Valid ∧
    (P.retainedRoute N hD havoid e).source =
      P.movedPosition N D ((P.finishedGraph N D).left e.val) ∧
    (P.retainedRoute N hD havoid e).target =
      P.movedPosition N D ((P.finishedGraph N D).right e.val) :=
  Classical.choose_spec (P.geometry_route_exists (P.retained_geometry N hD havoid e))

end QMAPortRouteData
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

theorem qmaPortOpposite_involutive (a : Fin 4) : qmaPortOpposite (qmaPortOpposite a) = a := by
  fin_cases a <;> rfl

theorem qmaGridNeighbor_opposite (p : ℕ × ℕ) (hp : 0 < p.1 ∧ 0 < p.2) (a : Fin 4) :
    qmaGridNeighbor (qmaGridNeighbor p a) (qmaPortOpposite a) = p := by
  fin_cases a
  · exact Prod.ext (Nat.add_sub_cancel p.1 1) rfl
  · exact Prod.ext rfl (Nat.add_sub_cancel p.2 1)
  · exact Prod.ext (by change p.1-1+1 = p.1; omega) rfl
  · exact Prod.ext rfl (by change p.2-1+1 = p.2; omega)

def qmaCorridorHalfCell (p : ℕ × ℕ) (a : Fin 4) (t : Fin 2) : ℕ × ℕ :=
  if t = 0 then p else qmaGridNeighbor p a

def qmaCorridorHalfPort (a : Fin 4) (t : Fin 2) : Fin 4 := if t = 0 then a else qmaPortOpposite a

def qmaCorridorEndPair (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    (p : ℕ × ℕ) (a : Fin 4) : Sym2 (ℕ × ℕ) :=
  s(qmaMovedPort cross p a,qmaMovedPort cross (qmaGridNeighbor p a) (qmaPortOpposite a))

theorem qmaCorridorEndPair_reverse (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    (p : ℕ × ℕ) (hp : 0 < p.1 ∧ 0 < p.2) (a : Fin 4) :
    qmaCorridorEndPair cross (qmaGridNeighbor p a) (qmaPortOpposite a) = qmaCorridorEndPair cross p a := by
  unfold qmaCorridorEndPair
  rw [qmaGridNeighbor_opposite p hp a,qmaPortOpposite_involutive]
  exact Sym2.eq_swap

theorem qmaCellCorridor_mem_half {p z : ℕ × ℕ} {a : Fin 4} {b c : Bool}
    (hz : z ∈ qmaCellCorridor p a b c) :
    ∃ t : Fin 2, z ∈ qmaHalfPathAt (qmaCorridorHalfCell p a t)
      (qmaCorridorHalfMode b c t) (qmaCorridorHalfPort a t) := by
  rcases List.mem_append.mp hz with h | h
  · exact ⟨0,h⟩
  · exact ⟨1,List.mem_reverse.mp h⟩

theorem qmaCorridorBody_half_pair (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    (p : ℕ × ℕ) (hp : 0 < p.1 ∧ 0 < p.2) (a : Fin 4) (b c : Bool)
    (hb : b = decide (cross p)) (hc : c = decide (cross (qmaGridNeighbor p a))) (t : Fin 2) :
    s((QMACellRouteBody.corridor p a b c).source,(QMACellRouteBody.corridor p a b c).target) =
      qmaCorridorEndPair cross (qmaCorridorHalfCell p a t) (qmaCorridorHalfPort a t) := by
  have h0 : s((QMACellRouteBody.corridor p a b c).source,
      (QMACellRouteBody.corridor p a b c).target) = qmaCorridorEndPair cross p a := by
    change s(qmaCellTranslate p (qmaLocalPort b a),
      qmaCellTranslate (qmaGridNeighbor p a) (qmaLocalPort c (qmaPortOpposite a))) = _
    rw [hb,hc,← qmaMovedPort_local,← qmaMovedPort_local]
    rfl
  fin_cases t
  · exact h0
  · exact h0.trans (qmaCorridorEndPair_reverse cross p hp a).symm

theorem qmaCorridorHalf_mode (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    (p : ℕ × ℕ) (a : Fin 4) (b c : Bool)
    (hb : b = decide (cross p)) (hc : c = decide (cross (qmaGridNeighbor p a))) (t : Fin 2) :
    qmaCorridorHalfMode b c t = decide (cross (qmaCorridorHalfCell p a t)) := by
  fin_cases t
  · exact hb
  · exact hc

theorem qmaHalfPathAt_collision (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    {p q z : ℕ × ℕ} {a d : Fin 4} {b c : Bool}
    (hb : b = decide (cross p)) (hc : c = decide (cross q))
    (hz : z ∈ qmaHalfPathAt p b a) (hw : z ∈ qmaHalfPathAt q c d) : p = q ∧ a = d := by
  obtain ⟨u,hu,heu⟩ := List.mem_map.mp hz
  obtain ⟨v,hv,hev⟩ := List.mem_map.mp hw
  have hh := qmaCellTranslate_unique (qmaHalfCorridor_bounded b a u hu)
    (qmaHalfCorridor_bounded c d v hv) (heu.trans hev.symm)
  rcases hh with ⟨rfl,rfl⟩
  have hbc : b = c := hb.trans hc.symm
  have hv' : u ∈ qmaHalfCorridorPath b d := by rw [hbc]; exact hv
  refine ⟨rfl,?_⟩
  by_contra had
  exact Finset.disjoint_left.mp (qmaHalfCorridor_disjoint b a d had)
    (List.mem_toFinset.mpr hu) (List.mem_toFinset.mpr hv')

end ContinuumCoulomb

end

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

theorem qmaCellPair_pair_injective : Function.Injective
    (fun e : Fin 6 => s(qmaCellPairLeft e,qmaCellPairRight e)) := by decide

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem routingPair_index {p : ℕ × ℕ} {e : Fin 6} (h : P.RoutingAllowed (.pair p e)) :
    ∃ i : P.Interior, P.cell i = p ∧ e = P.cellPairIndex i := by
  obtain ⟨_,i,hi,hp⟩ := h
  refine ⟨i,hi,qmaCellPair_pair_injective ?_⟩
  exact hp.symm.trans (P.cellPairIndex_pair i).symm

theorem internal_allowed_disjoint
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (p : ℕ × ℕ) (e f : QMAInternalEdge) (hef : e ≠ f)
    (he : P.RoutingAllowed (qmaInternalBody p e))
    (hf : P.RoutingAllowed (qmaInternalBody p f)) :
    Disjoint (((qmaInternalPath e).drop 1).dropLast).toFinset (qmaInternalPath f).toFinset := by
  rcases e with a | (a | a) <;> rcases f with b | (b | b)
  · change Disjoint (((qmaCellRayPath a).drop 1).dropLast).toFinset (qmaCellRayPath b).toFinset
    fin_cases a <;> fin_cases b <;> first | exact (hef rfl).elim | decide
  · obtain ⟨⟨v,hv⟩,_⟩ := he
    obtain ⟨_,i,hi,_⟩ := hf
    exact (havoid i v (hi.trans hv.symm)).elim
  · exact (he.2 hf).elim
  · obtain ⟨_,i,hi,_⟩ := he
    obtain ⟨⟨v,hv⟩,_⟩ := hf
    exact (havoid i v (hi.trans hv.symm)).elim
  · obtain ⟨i,hi,rfl⟩ := P.routingPair_index he
    obtain ⟨j,hj,rfl⟩ := P.routingPair_index hf
    have hij : i ≠ j := by
      intro h
      apply hef
      rw [h]
    have hn : ¬P.IsCrossing (P.cell i) := by simpa only [hi] using he.1
    have hd := P.ordinary_visit_paths_disjoint hij (hi.trans hj.symm) hn
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    apply Finset.disjoint_left.mp hd _ hz'
    exact List.mem_toFinset.mpr
      (List.mem_of_mem_drop (List.mem_of_mem_dropLast (List.mem_toFinset.mp hz)))
  · exact (he.1 hf).elim
  · exact (hf.2 he).elim
  · exact (hf.1 he).elim
  · change Disjoint (((qmaLocalPatchPath a).drop 1).dropLast).toFinset (qmaLocalPatchPath b).toFinset
    fin_cases a <;> fin_cases b <;> first | exact (hef rfl).elim | decide

end QMAPortRouteData
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

theorem qmaRoute_path_finset (R : QMACellRoute) : R.path.toFinset = R.body.path.toFinset := by
  rcases R with ⟨b,r⟩
  cases r
  · rfl
  · exact List.toFinset_reverse

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

theorem qmaCellCorridor_interior {p z : ℕ × ℕ} (hp : 0 < p.1 ∧ 0 < p.2)
    {a : Fin 4} {b c : Bool} (hz : z ∈ ((qmaCellCorridor p a b c).drop 1).dropLast) :
    z ∈ (qmaHalfPathAt p b a).drop 1 ∨
      z ∈ (qmaHalfPathAt (qmaGridNeighbor p a) c (qmaPortOpposite a)).drop 1 := by
  have hs := qmaCellCorridor_simple p hp a b c
  have hfirst := qmaListInterior_ne_head hs (qmaCellCorridor_endpoints p a b c).1 hz
  have hlast := qmaListInterior_ne_last hs (qmaCellCorridor_endpoints p a b c).2 hz
  have hm := List.mem_of_mem_drop (List.mem_of_mem_dropLast hz)
  rcases List.mem_append.mp hm with h | h
  · exact Or.inl (qmaList_mem_drop_one (qmaHalfPathAt_endpoints p b a).1 h hfirst)
  · exact Or.inr (qmaList_mem_drop_one
      (qmaHalfPathAt_endpoints (qmaGridNeighbor p a) c (qmaPortOpposite a)).1
      (List.mem_reverse.mp h) hlast)

end ContinuumCoulomb

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

theorem half_internal_disjoint (p : ℕ × ℕ) (e : QMAInternalEdge) (a : Fin 4)
    (b : Bool) (he : P.RoutingAllowed (qmaInternalBody p e)) (hb : b = decide (P.IsCrossing p)) :
    Disjoint ((qmaHalfCorridorPath b a).drop 1).toFinset (qmaInternalPath e).toFinset := by
  subst b
  rcases e with e | (e | e)
  · have hn : ¬P.IsCrossing p := he.2
    simpa only [qmaInternalPath,hn,decide_false] using qmaHalfCorridor_ray a e
  · have hn : ¬P.IsCrossing p := he.1
    simpa only [qmaInternalPath,hn,decide_false] using qmaHalfCorridor_pair a e
  · have hp : P.IsCrossing p := he
    simpa only [qmaInternalPath,hp,decide_true] using qmaHalfCorridor_patch a e

theorem halfAt_internal_disjoint (p q : ℕ × ℕ) (a : Fin 4) (b : Bool) (e : QMAInternalEdge)
    (he : P.RoutingAllowed (qmaInternalBody q e)) (hb : b = decide (P.IsCrossing p)) :
    Disjoint ((qmaHalfPathAt p b a).drop 1).toFinset (qmaInternalBody q e).path.toFinset := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  have hz' := List.mem_toFinset.mp hz
  change z ∈ ((qmaHalfCorridorPath b a).map (qmaCellTranslate p)).drop 1 at hz'
  rw [← List.map_drop] at hz'
  have hw' := List.mem_toFinset.mp hw
  rw [qmaInternalBody_path] at hw'
  obtain ⟨u,hu,heu⟩ := List.mem_map.mp hz'
  obtain ⟨v,hv,hev⟩ := List.mem_map.mp hw'
  have hh := qmaCellTranslate_unique (qmaHalfCorridor_bounded b a u (List.mem_of_mem_drop hu))
    (qmaInternalPath_bounded e v hv) (heu.trans hev.symm)
  rcases hh with ⟨rfl,rfl⟩
  exact Finset.disjoint_left.mp (P.half_internal_disjoint p e a b he hb)
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

theorem corridor_internal_disjoint (p q : ℕ × ℕ) (a : Fin 4) (b c : Bool) (e : QMAInternalEdge)
    (hp : 0 < p.1 ∧ 0 < p.2) (hc : P.RoutingAllowed (.corridor p a b c))
    (he : P.RoutingAllowed (qmaInternalBody q e)) :
    Disjoint (((qmaCellCorridor p a b c).drop 1).dropLast).toFinset
      (qmaInternalBody q e).path.toFinset := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  rcases qmaCellCorridor_interior hp (List.mem_toFinset.mp hz) with h | h
  · exact Finset.disjoint_left.mp (P.halfAt_internal_disjoint p q a b e he hc.1)
      (List.mem_toFinset.mpr h) hw
  · exact Finset.disjoint_left.mp (P.halfAt_internal_disjoint (qmaGridNeighbor p a) q
      (qmaPortOpposite a) c e he hc.2) (List.mem_toFinset.mpr h) hw

theorem corridors_disjoint (p q : ℕ × ℕ) (a d : Fin 4) (b c f g : Bool)
    (hp : 0 < p.1 ∧ 0 < p.2) (hq : 0 < q.1 ∧ 0 < q.2)
    (hR : P.RoutingAllowed (.corridor p a b c)) (hS : P.RoutingAllowed (.corridor q d f g))
    (hne : s((QMACellRouteBody.corridor p a b c).source,(QMACellRouteBody.corridor p a b c).target) ≠
      s((QMACellRouteBody.corridor q d f g).source,(QMACellRouteBody.corridor q d f g).target)) :
    Disjoint (qmaCellCorridor p a b c).toFinset (qmaCellCorridor q d f g).toFinset := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  obtain ⟨t,ht⟩ := qmaCellCorridor_mem_half (List.mem_toFinset.mp hz)
  obtain ⟨u,hu⟩ := qmaCellCorridor_mem_half (List.mem_toFinset.mp hw)
  have hc := qmaHalfPathAt_collision P.IsCrossing
    (qmaCorridorHalf_mode P.IsCrossing p a b c hR.1 hR.2 t)
    (qmaCorridorHalf_mode P.IsCrossing q d f g hS.1 hS.2 u) ht hu
  apply hne
  rw [qmaCorridorBody_half_pair P.IsCrossing p hp a b c hR.1 hR.2 t,
    qmaCorridorBody_half_pair P.IsCrossing q hq d f g hS.1 hS.2 u,hc.1,hc.2]

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPatchPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nine ordinary physical gadget edges are exactly the fixed patch edges,
with only the west-south perimeter edge oriented in reverse. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph

def qmaPatchPhysicalVertex {n r : ℕ} (site : Fin r → Fin 4 → Fin n) (i : Fin r) : Fin 6 → Fin (n+r*2) :=
  ![old n r (site i 0),old n r (site i 1),old n r (site i 2),old n r (site i 3),
    fresh n r i 0,fresh n r i 1]

def qmaPatchPhysicalEdge {ν : Type*} {r : ℕ} (i : Fin r) : Fin 9 → QMACrossingsGraphEdge ν r :=
  ![.inr (.inl i),.inr (.inr (i,0)),.inr (.inr (i,1)),.inr (.inr (i,2)),.inr (.inr (i,3)),
    .inl (.inr (i,0)),.inl (.inr (i,2)),.inl (.inr (i,3)),.inl (.inr (i,1))]

def qmaPatchSource (e : Fin 9) : Fin 6 := if e = 8 then qmaCrossingPatchRight e else qmaCrossingPatchLeft e

def qmaPatchTarget (e : Fin 9) : Fin 6 := if e = 8 then qmaCrossingPatchLeft e else qmaCrossingPatchRight e

theorem qmaPatchPhysical_left {ν : Type*} {n r : ℕ} (left : ν → Fin n)
    (site : Fin r → Fin 4 → Fin n) (i : Fin r) (e : Fin 9) :
    qmaParallelGraphLeft (qmaCrossingsBaseLeft left site) site (qmaPatchPhysicalEdge i e) =
      qmaPatchPhysicalVertex site i (qmaPatchSource e) := by
  fin_cases e <;> rfl

theorem qmaPatchPhysical_right {ν : Type*} {n r : ℕ} (right : ν → Fin n)
    (site : Fin r → Fin 4 → Fin n) (i : Fin r) (e : Fin 9) :
    qmaParallelGraphRight (qmaCrossingsBaseRight right site) (fun _ => qmaCrossingMember)
      (qmaPatchPhysicalEdge i e) = qmaPatchPhysicalVertex site i (qmaPatchTarget e) := by
  fin_cases e <;> rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingPatchChart
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each selected gadget's six physical spins occupy exactly the six vertices
of the explicit translated planar patch. -/

noncomputable section
namespace ContinuumCoulomb
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem crossingPosition_patchVertex (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (i : Fin P.crossingCells.card) (v : Fin 6) :
    P.crossingPosition N D (qmaPatchPhysicalVertex (P.crossingSiteFin N hD) i v) =
      qmaPatchTranslate (P.crossingCell i).val (qmaCrossingPatchVertex v) := by
  fin_cases v <;> simp [qmaPatchPhysicalVertex,P.crossingPosition_old,P.crossingPosition_fresh,
    crossingSiteFin,movedPosition_site,freshCrossingPosition,qmaInnerPort,qmaGadgetAncilla,
    qmaPatchDirection,qmaPatchTranslate,qmaCrossingPatchVertex,Nat.add_assoc]

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPatchEdgeCover
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMACellRoute.reverse_body _root_.OAI.ContinuumCoulomb.QMACellRoute.reverse_source _root_.OAI.ContinuumCoulomb.QMACellRoute.reverse_target _root_.OAI.ContinuumCoulomb.QMACellRoute.reverse_valid _root_.OAI.ContinuumCoulomb.qmaPointCell_center _root_.OAI.ContinuumCoulomb.qmaPointCell_port _root_.OAI.ContinuumCoulomb.qmaPortChain_last _root_.OAI.ContinuumCoulomb.qmaPortChain_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical output has retained edges and exactly the nine enumerated edges
at each gadget. The last perimeter edge uses the reversed catalog path. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaCrossingsEdge_cover {ν : Type*} {r : ℕ} (e : QMACrossingsGraphEdge ν r) :
    (∃ f : ν, e = .inl (.inl f)) ∨ ∃ i k, e = qmaPatchPhysicalEdge i k := by
  rcases e with (e | ⟨i,a⟩) | (i | ⟨i,a⟩)
  · exact Or.inl ⟨e,rfl⟩
  · apply Or.inr
    fin_cases a
    · exact ⟨i,5,rfl⟩
    · exact ⟨i,8,rfl⟩
    · exact ⟨i,6,rfl⟩
    · exact ⟨i,7,rfl⟩
  · exact Or.inr ⟨i,0,rfl⟩
  · apply Or.inr
    fin_cases a
    · exact ⟨i,1,rfl⟩
    · exact ⟨i,2,rfl⟩
    · exact ⟨i,3,rfl⟩
    · exact ⟨i,4,rfl⟩

def qmaPatchRoute (p : ℕ × ℕ) (k : Fin 9) : QMACellRoute :=
  ⟨.patch p k,decide (k = 8)⟩

theorem qmaPatchRoute_source (p : ℕ × ℕ) (k : Fin 9) :
    (qmaPatchRoute p k).source = qmaPatchTranslate p (qmaCrossingPatchVertex (qmaPatchSource k)) := by
  by_cases h : k = 8 <;>
    simp [qmaPatchRoute,QMACellRoute.source,QMACellRouteBody.source,QMACellRouteBody.target,qmaPatchSource,h]

theorem qmaPatchRoute_target (p : ℕ × ℕ) (k : Fin 9) :
    (qmaPatchRoute p k).target = qmaPatchTranslate p (qmaCrossingPatchVertex (qmaPatchTarget k)) := by
  by_cases h : k = 8 <;>
    simp [qmaPatchRoute,QMACellRoute.target,QMACellRouteBody.source,QMACellRouteBody.target,qmaPatchTarget,h]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCrossingOutputRoutes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every edge of the actual simultaneous crossing output has a short permitted
lattice route with the exact physical endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

abbrev crossingOutput (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) :=
  (P.portCrossingSelection N hD).layer.output N

theorem crossingOutput_route_exists (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.crossingOutput N hD).Edge) :
    ∃ R : QMACellRoute, P.RoutingAllowed R.body ∧ R.Valid ∧
      R.source = P.crossingPosition N D ((P.crossingOutput N hD).left e) ∧
      R.target = P.crossingPosition N D ((P.crossingOutput N hD).right e) := by
  rcases qmaCrossingsEdge_cover e with ⟨f,rfl⟩ | ⟨i,k,rfl⟩
  · let R := P.retainedRoute N hD havoid f
    have hs := P.retainedRoute_spec N hD havoid f
    refine ⟨R,hs.1,hs.2.1,?_,?_⟩
    · change R.source = P.crossingPosition N D
        (old (P.finishedGraph N D).n P.crossingCells.card ((P.finishedGraph N D).left f.val))
      rw [P.crossingPosition_old]
      exact hs.2.2.1
    · change R.target = P.crossingPosition N D
        (old (P.finishedGraph N D).n P.crossingCells.card ((P.finishedGraph N D).right f.val))
      rw [P.crossingPosition_old]
      exact hs.2.2.2
  · refine ⟨qmaPatchRoute (P.crossingCell i).val k,?_,trivial,?_,?_⟩
    · exact P.mem_crossingCells.mp (P.crossingCell i).property
    · rw [qmaPatchRoute_source]
      change _ = P.crossingPosition N D
        (qmaParallelGraphLeft (qmaCrossingsBaseLeft (P.portCrossingSelection N hD).retained.left
          (P.crossingSiteFin N hD)) (P.crossingSiteFin N hD) (qmaPatchPhysicalEdge i k))
      rw [qmaPatchPhysical_left]
      exact (P.crossingPosition_patchVertex N hD i (qmaPatchSource k)).symm
    · rw [qmaPatchRoute_target]
      change _ = P.crossingPosition N D
        (qmaParallelGraphRight (qmaCrossingsBaseRight (P.portCrossingSelection N hD).retained.right
          (P.crossingSiteFin N hD)) (fun _ => qmaCrossingMember) (qmaPatchPhysicalEdge i k))
      rw [qmaPatchPhysical_right]
      exact (P.crossingPosition_patchVertex N hD i (qmaPatchTarget k)).symm

end QMAPortRouteData
end ContinuumCoulomb

end

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

theorem qmaManhattanPoint_support (p q : ℕ × ℕ) (k : ℕ)
    (hk : k ≤ qmaManhattanLength p q) : qmaManhattanSupport p q (qmaManhattanPoint p q k) := by
  by_cases hx : k ≤ Nat.dist p.1 q.1
  · left
    simp only [qmaManhattanPoint,ite_eq_left hx]
    exact ⟨True.intro,qmaAxisWalk_bounds _ _ _ hx⟩
  · right
    have hy : k-Nat.dist p.1 q.1 ≤ Nat.dist p.2 q.2 := by
      unfold qmaManhattanLength at hk
      omega
    simp only [qmaManhattanPoint,ite_eq_right hx]
    exact ⟨True.intro,qmaAxisWalk_bounds _ _ _ hy⟩

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRouteLeaf
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reserve one singlet leaf beside the initial step of every scaled route.
Four incident directions use four different quadrants. -/

namespace ContinuumCoulomb

theorem qmaRouteLeaf_step (p : ℕ × ℕ) (a : Fin 4) :
    qmaSquareGrid.Adj (qmaLeafFirst p a) (qmaRouteLeaf p a) := by
  fin_cases a <;> simp [qmaSquareGrid,qmaLeafFirst,qmaRouteLeaf,Nat.dist]

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumScaledEdge
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.qmaFineRoute_last _root_.OAI.ContinuumCoulomb.qmaFineRoute_nat _root_.OAI.ContinuumCoulomb.qmaFineRoute_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eightfold unit-edge corridors leave the diagonal leaf sites free. -/

namespace ContinuumCoulomb

theorem qmaLeafCenter_length (p q : ℕ × ℕ) :
    qmaManhattanLength (qmaLeafCenter p) (qmaLeafCenter q) = 8*qmaManhattanLength p q := by
  simp only [qmaManhattanLength,qmaLeafCenter,Nat.dist_add_add_right,Nat.dist_mul_left,Nat.mul_add]

theorem qmaLeafCenter_adj_length {p q : ℕ × ℕ} (h : qmaSquareGrid.Adj p q) :
    qmaManhattanLength (qmaLeafCenter p) (qmaLeafCenter q) = 8 := by
  rw [qmaLeafCenter_length]
  change qmaManhattanLength p q = 1 at h
  omega

theorem qmaLeafCenter_point_gridline (p q : ℕ × ℕ) (k : ℕ)
    (hk : k ≤ qmaManhattanLength (qmaLeafCenter p) (qmaLeafCenter q)) :
    (qmaManhattanPoint (qmaLeafCenter p) (qmaLeafCenter q) k).1%8 = 4 ∨
      (qmaManhattanPoint (qmaLeafCenter p) (qmaLeafCenter q) k).2%8 = 4 := by
  have h := qmaManhattanPoint_support (qmaLeafCenter p) (qmaLeafCenter q) k hk
  rcases h with ⟨hy,_⟩ | ⟨hx,_⟩
  · right
    rw [hy]
    simp [qmaLeafCenter,Nat.add_mod]
  · left
    rw [hx]
    simp [qmaLeafCenter,Nat.add_mod]

theorem qmaLeafCenter_point_one (p : ℕ × ℕ) (hx : 0 < p.1) (hy : 0 < p.2) (a : Fin 4) :
    qmaManhattanPoint (qmaLeafCenter p) (qmaLeafCenter (qmaGridNeighbor p a)) 1 = qmaLeafFirst p a := by
  have hpx : p.1-1+1 = p.1 := by omega
  have hpy : p.2-1+1 = p.2 := by omega
  fin_cases a <;> simp [qmaManhattanPoint,qmaAxisWalk,qmaLeafCenter,qmaGridNeighbor,qmaLeafFirst,Nat.dist]
  all_goals first | omega | (split_ifs <;> simp only [Prod.mk.injEq] <;> omega)

theorem qmaLeafCenter_point_first {p q : ℕ × ℕ} (hx : 0 < p.1) (hy : 0 < p.2)
    (ha : qmaSquareGrid.Adj p q) :
    qmaManhattanPoint (qmaLeafCenter p) (qmaLeafCenter q) 1 =
      qmaLeafFirst p (qmaGridNeighborIndex p q) := by
  simpa only [qmaGridNeighborIndex_spec hx hy ha] using
    qmaLeafCenter_point_one p hx hy (qmaGridNeighborIndex p q)

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumScaledDirection
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.qmaFineRoute_nat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior points of two scaled unit segments can coincide only when the
underlying grid edge is the same, possibly with reversed orientation. -/

namespace ContinuumCoulomb

theorem qmaScaledDirectionPoint_eq (p : ℕ × ℕ) (hx : 0 < p.1) (hy : 0 < p.2)
    (a : Fin 4) {k : ℕ} (hk : k ≤ 8) :
    qmaManhattanPoint (qmaLeafCenter p) (qmaLeafCenter (qmaGridNeighbor p a)) k =
      qmaScaledDirectionPoint p a k := by
  have hpx : p.1-1+1 = p.1 := by omega
  have hpy : p.2-1+1 = p.2 := by omega
  fin_cases a <;> simp [qmaManhattanPoint,qmaAxisWalk,qmaLeafCenter,qmaGridNeighbor,
    qmaScaledDirectionPoint,Nat.dist]
  all_goals first | omega | (split_ifs <;> simp only [Prod.mk.injEq] <;> omega)

theorem qmaScaledDirectionPoint_collision (p r : ℕ × ℕ)
    (hpx : 0 < p.1) (hpy : 0 < p.2) (hrx : 0 < r.1) (hry : 0 < r.2)
    (a b : Fin 4) {i j : ℕ} (hi : 0 < i) (hi8 : i < 8) (hj : 0 < j) (hj8 : j < 8)
    (h : qmaScaledDirectionPoint p a i = qmaScaledDirectionPoint r b j) :
    (p = r ∧ qmaGridNeighbor p a = qmaGridNeighbor r b) ∨
      (p = qmaGridNeighbor r b ∧ qmaGridNeighbor p a = r) := by
  rcases p with ⟨x,y⟩
  rcases r with ⟨u,v⟩
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  fin_cases a <;> fin_cases b <;>
    simp [qmaScaledDirectionPoint,qmaGridNeighbor,Prod.mk.injEq] at h1 h2 ⊢ <;> omega

theorem qmaScaledEdge_inner_collision {p q r s : ℕ × ℕ}
    (hp : 0 < p.1 ∧ 0 < p.2) (hr : 0 < r.1 ∧ 0 < r.2)
    (hpq : qmaSquareGrid.Adj p q) (hrs : qmaSquareGrid.Adj r s)
    {i j : ℕ} (hi : 0 < i) (hi8 : i < 8) (hj : 0 < j) (hj8 : j < 8)
    (h : qmaManhattanPoint (qmaLeafCenter p) (qmaLeafCenter q) i =
      qmaManhattanPoint (qmaLeafCenter r) (qmaLeafCenter s) j) :
    (p = r ∧ q = s) ∨ (p = s ∧ q = r) := by
  obtain ⟨a,rfl⟩ := qmaGridNeighbor_exists hpq
  obtain ⟨b,rfl⟩ := qmaGridNeighbor_exists hrs
  rw [qmaScaledDirectionPoint_eq p hp.1 hp.2 a hi8.le,
    qmaScaledDirectionPoint_eq r hr.1 hr.2 b hj8.le] at h
  exact qmaScaledDirectionPoint_collision p r hp.1 hp.2 hr.1 hr.2 a b hi hi8 hj hj8 h

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumInflatedPath
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.qmaFineRoute_last _root_.OAI.ContinuumCoulomb.qmaFineRoute_nat _root_.OAI.ContinuumCoulomb.qmaFineRoute_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replace each unit edge of a simple path by its eight-step corridor. -/

namespace ContinuumCoulomb

def qmaInflatedPoint (p : ℕ → ℕ × ℕ) (k : ℕ) : ℕ × ℕ :=
  qmaManhattanPoint (qmaLeafCenter (p (k/8))) (qmaLeafCenter (p (k/8+1))) (k%8)

@[simp] theorem qmaInflatedPoint_zero (p : ℕ → ℕ × ℕ) :
    qmaInflatedPoint p 0 = qmaLeafCenter (p 0) := by simp [qmaInflatedPoint]

theorem qmaInflatedPoint_boundary (p : ℕ → ℕ × ℕ) {k : ℕ} (hk : k%8 = 0) :
    qmaInflatedPoint p k = qmaLeafCenter (p (k/8)) := by
  simp only [qmaInflatedPoint,hk,qmaManhattanPoint_zero]

@[simp] theorem qmaInflatedPoint_last (p : ℕ → ℕ × ℕ) (L : ℕ) :
    qmaInflatedPoint p (8*L) = qmaLeafCenter (p L) := by
  simp [qmaInflatedPoint]

theorem qmaLeafCenter_injective : Function.Injective qmaLeafCenter := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext <;> simp only [qmaLeafCenter] at hx hy <;> omega

theorem qmaInflatedPoint_step (p : ℕ → ℕ × ℕ) {L : ℕ}
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1))) {k : ℕ} (hk : k < 8*L) :
    qmaSquareGrid.Adj (qmaInflatedPoint p k) (qmaInflatedPoint p (k+1)) := by
  have hdiv : k/8 < L := by omega
  have hlen := qmaLeafCenter_adj_length (hp _ hdiv)
  have hm : k%8 < 8 := Nat.mod_lt _ (by decide)
  by_cases h7 : k%8 = 7
  · have hq : (k+1)/8 = k/8+1 := by omega
    have hr : (k+1)%8 = 0 := by omega
    have hs := qmaManhattanPoint_adj (qmaLeafCenter (p (k/8)))
      (qmaLeafCenter (p (k/8+1))) 7 (by omega)
    have he := qmaManhattanPoint_last (qmaLeafCenter (p (k/8))) (qmaLeafCenter (p (k/8+1)))
    rw [hlen] at he
    change qmaSquareGrid.Adj
      (qmaManhattanPoint (qmaLeafCenter (p (k/8))) (qmaLeafCenter (p (k/8+1))) 7)
      (qmaManhattanPoint (qmaLeafCenter (p (k/8))) (qmaLeafCenter (p (k/8+1))) 8) at hs
    rw [he] at hs
    simpa only [qmaInflatedPoint,h7,hq,hr,qmaManhattanPoint_zero] using hs
  · have hq : (k+1)/8 = k/8 := by omega
    have hr : (k+1)%8 = k%8+1 := by omega
    simpa only [qmaInflatedPoint,hq,hr] using
      qmaManhattanPoint_adj (qmaLeafCenter (p (k/8)))
        (qmaLeafCenter (p (k/8+1))) (k%8) (by omega)

theorem qmaInflatedPoint_gridline (p : ℕ → ℕ × ℕ) {L : ℕ}
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1))) {k : ℕ} (hk : k ≤ 8*L) :
    (qmaInflatedPoint p k).1%8 = 4 ∨ (qmaInflatedPoint p k).2%8 = 4 := by
  by_cases h0 : k%8 = 0
  · rw [qmaInflatedPoint_boundary p h0]
    left
    simp [qmaLeafCenter,Nat.add_mod]
  · have hdiv : k/8 < L := by omega
    have hlen := qmaLeafCenter_adj_length (hp _ hdiv)
    exact qmaLeafCenter_point_gridline _ _ _ (by omega)

theorem qmaInflatedPoint_not_center (p : ℕ → ℕ × ℕ) {L : ℕ}
    (hpos : ∀ i ≤ L, 0 < (p i).1 ∧ 0 < (p i).2)
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1))) {k : ℕ}
    (hk : k ≤ 8*L) (h0 : k%8 ≠ 0) (r : ℕ × ℕ) :
    qmaInflatedPoint p k ≠ qmaLeafCenter r := by
  have hdiv : k/8 < L := by omega
  obtain ⟨a,ha⟩ := qmaGridNeighbor_exists (hp _ hdiv)
  change qmaManhattanPoint (qmaLeafCenter (p (k/8))) (qmaLeafCenter (p (k/8+1))) (k%8) ≠ _
  rw [← ha,qmaScaledDirectionPoint_eq _ (hpos _ hdiv.le).1 (hpos _ hdiv.le).2 a
    (Nat.le_of_lt (Nat.mod_lt _ (by decide)))]
  exact qmaScaledDirectionPoint_not_center _ r a
    (by omega) (Nat.mod_lt _ (by decide))

theorem qmaInflatedPoint_injective (p : ℕ → ℕ × ℕ) {L : ℕ}
    (hpos : ∀ i ≤ L, 0 < (p i).1 ∧ 0 < (p i).2)
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1)))
    (hs : ∀ i j, i ≤ L → j ≤ L → p i = p j → i = j)
    {i j : ℕ} (hi : i ≤ 8*L) (hj : j ≤ 8*L)
    (h : qmaInflatedPoint p i = qmaInflatedPoint p j) : i = j := by
  by_cases hi0 : i%8 = 0
  · rw [qmaInflatedPoint_boundary p hi0] at h
    by_cases hj0 : j%8 = 0
    · rw [qmaInflatedPoint_boundary p hj0] at h
      have he := hs (i/8) (j/8) (by omega) (by omega) (qmaLeafCenter_injective h)
      omega
    · exact (qmaInflatedPoint_not_center p hpos hp hj hj0 _ h.symm).elim
  · by_cases hj0 : j%8 = 0
    · rw [qmaInflatedPoint_boundary p hj0] at h
      exact (qmaInflatedPoint_not_center p hpos hp hi hi0 _ h).elim
    have hid : i/8 < L := by omega
    have hjd : j/8 < L := by omega
    have hip : 0 < i%8 := by omega
    have hjp : 0 < j%8 := by omega
    have hi8 := Nat.mod_lt i (by decide : 0 < 8)
    have hj8 := Nat.mod_lt j (by decide : 0 < 8)
    have hc := qmaScaledEdge_inner_collision (hpos _ hid.le) (hpos _ hjd.le)
      (hp _ hid) (hp _ hjd) hip hi8 hjp hj8 h
    rcases hc with ⟨ha,_⟩ | ⟨ha,hb⟩
    · have hd := hs (i/8) (j/8) hid.le hjd.le ha
      have hlen := qmaLeafCenter_adj_length (hp (i/8) hid)
      change qmaManhattanPoint (qmaLeafCenter (p (i/8))) (qmaLeafCenter (p (i/8+1))) (i%8) =
        qmaManhattanPoint (qmaLeafCenter (p (j/8))) (qmaLeafCenter (p (j/8+1))) (j%8) at h
      rw [← hd] at h
      have hm1 := qmaManhattanPoint_distance (qmaLeafCenter (p (i/8)))
        (qmaLeafCenter (p (i/8+1))) (i%8) (by omega)
      have hm2 := qmaManhattanPoint_distance (qmaLeafCenter (p (i/8)))
        (qmaLeafCenter (p (i/8+1))) (j%8) (by omega)
      rw [h] at hm1
      omega
    · have hd1 := hs (i/8) (j/8+1) hid.le (by omega) ha
      have hd2 := hs (i/8+1) (j/8) (by omega) hjd.le hb
      omega

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumInflatedSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inflating a planar route family preserves its disjoint interiors. -/

namespace ContinuumCoulomb

theorem qmaInflatedPoint_avoids_vertex (p : ℕ → ℕ × ℕ) {L : ℕ}
    (hpos : ∀ i ≤ L, 0 < (p i).1 ∧ 0 < (p i).2)
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1))) (v : ℕ × ℕ)
    (hv : ∀ i, 0 < i → i < L → p i ≠ v) {k : ℕ} (hk0 : 0 < k) (hk : k < 8*L) :
    qmaInflatedPoint p k ≠ qmaLeafCenter v := by
  by_cases h0 : k%8 = 0
  · rw [qmaInflatedPoint_boundary p h0]
    intro h
    exact hv (k/8) (by omega) (by omega) (qmaLeafCenter_injective h)
  · exact qmaInflatedPoint_not_center p hpos hp hk.le h0 v

theorem qmaInflatedPoint_disjoint (p q : ℕ → ℕ × ℕ) {L M : ℕ}
    (hp0 : ∀ i ≤ L, 0 < (p i).1 ∧ 0 < (p i).2)
    (hq0 : ∀ j ≤ M, 0 < (q j).1 ∧ 0 < (q j).2)
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1)))
    (hq : ∀ j < M, qmaSquareGrid.Adj (q j) (q (j+1)))
    (hd : ∀ i j, 0 < i → i < L → j ≤ M → p i ≠ q j)
    (he : ∀ i j, i < L → j < M →
      ¬(p i = q j ∧ p (i+1) = q (j+1)) ∧ ¬(p i = q (j+1) ∧ p (i+1) = q j))
    {i j : ℕ} (hi0 : 0 < i) (hi : i < 8*L) (hj : j ≤ 8*M) :
    qmaInflatedPoint p i ≠ qmaInflatedPoint q j := by
  intro h
  by_cases hiz : i%8 = 0
  · rw [qmaInflatedPoint_boundary p hiz] at h
    by_cases hjz : j%8 = 0
    · rw [qmaInflatedPoint_boundary q hjz] at h
      exact hd (i/8) (j/8) (by omega) (by omega) (by omega) (qmaLeafCenter_injective h)
    · exact qmaInflatedPoint_not_center q hq0 hq hj hjz _ h.symm
  · by_cases hjz : j%8 = 0
    · rw [qmaInflatedPoint_boundary q hjz] at h
      exact qmaInflatedPoint_not_center p hp0 hp hi.le hiz _ h
    have hid : i/8 < L := by omega
    have hjd : j/8 < M := by omega
    have hc := qmaScaledEdge_inner_collision (hp0 _ hid.le) (hq0 _ hjd.le)
      (hp _ hid) (hq _ hjd) (by omega : 0 < i%8) (Nat.mod_lt _ (by decide))
      (by omega : 0 < j%8) (Nat.mod_lt _ (by decide)) h
    exact hc.elim (he _ _ hid hjd).1 (he _ _ hid hjd).2

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact exchange-graph semantics for the finite bond lists manipulated by
the routing compiler. The scalar offset stays part of the full Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListGraph
open Matrix MediatorListProgram
open scoped BigOperators Classical

def ofBonds (n : ℕ) (xs : List Bond) (c : ℚ)
    (hb : SourceBondLists.bounded n xs) (hn : ∀ e ∈ xs, e.1 ≠ e.2.1) :
    QMARationalExchangeGraph where
  n := n
  Edge := Fin xs.length
  left := (SourceBondLists.bonds n xs hb).left
  right := (SourceBondLists.bonds n xs hb).right
  distinct := fun i h => hn _ (List.get_mem xs i) (congrArg Fin.val h)
  weight := (SourceBondLists.bonds n xs hb).weight
  constant := c

end ContinuumCoulomb.QuantumListGraph

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

abbrev Output := ℕ × (List Bond × ℚ)

end ContinuumCoulomb.QuantumListPathStep

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

def orderedPair (G : QMARationalExchangeGraph) (e : G.Edge) : Fin G.n × Fin G.n :=
  (min (G.left e) (G.right e),max (G.left e) (G.right e))

def edgePairs (G : QMARationalExchangeGraph) : Finset (Fin G.n × Fin G.n) :=
  Finset.univ.image G.orderedPair

abbrev MergedEdge (G : QMARationalExchangeGraph) := {p // p ∈ G.edgePairs}

def edgeClass (G : QMARationalExchangeGraph) (e : G.Edge) : G.MergedEdge :=
  ⟨G.orderedPair e,Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩⟩

theorem orderedPair_lt (G : QMARationalExchangeGraph) (e : G.Edge) :
    (G.orderedPair e).1 < (G.orderedPair e).2 := by
  rcases lt_or_gt_of_ne (G.distinct e) with h | h
  · simpa only [orderedPair,min_eq_left h.le,max_eq_right h.le] using h
  · simpa only [orderedPair,min_eq_right h.le,max_eq_left h.le] using h

theorem mergedEdge_lt (G : QMARationalExchangeGraph) (p : G.MergedEdge) : p.val.1 < p.val.2 := by
  obtain ⟨e,_,he⟩ := Finset.mem_image.mp p.property
  rw [← he]
  exact G.orderedPair_lt e

def merge (G : QMARationalExchangeGraph) : QMARationalExchangeGraph where
  n := G.n
  Edge := G.MergedEdge
  left := fun p => p.val.1
  right := fun p => p.val.2
  distinct := fun p => (G.mergedEdge_lt p).ne
  weight := fun p => ∑ e, if G.edgeClass e = p then G.weight e else 0
  constant := G.constant

theorem merge_edge_source (G : QMARationalExchangeGraph) (p : G.merge.Edge) :
    ∃ e : G.Edge, (G.merge.left p = G.left e ∧ G.merge.right p = G.right e) ∨
      (G.merge.left p = G.right e ∧ G.merge.right p = G.left e) := by
  obtain ⟨e,_,he⟩ := Finset.mem_image.mp p.property
  refine ⟨e,?_⟩
  change (p.val.1 = G.left e ∧ p.val.2 = G.right e) ∨
    (p.val.1 = G.right e ∧ p.val.2 = G.left e)
  rw [← he]
  rcases le_total (G.left e) (G.right e) with h | h
  · exact Or.inl ⟨min_eq_left h,max_eq_right h⟩
  · exact Or.inr ⟨min_eq_right h,max_eq_left h⟩

end QMARationalExchangeGraph
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumMergedOutputRoutes
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
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem mergedOutput_route_exists (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.crossingOutput N hD).merge.Edge) :
    ∃ R : QMACellRoute, P.RoutingAllowed R.body ∧ R.Valid ∧
      R.source = P.crossingPosition N D ((P.crossingOutput N hD).merge.left e) ∧
      R.target = P.crossingPosition N D ((P.crossingOutput N hD).merge.right e) := by
  obtain ⟨f,hf⟩ := (P.crossingOutput N hD).merge_edge_source e
  obtain ⟨R,hR,hv,hl,hr⟩ := P.crossingOutput_route_exists N hD havoid f
  rcases hf with ⟨hleft,hright⟩ | ⟨hleft,hright⟩
  · exact ⟨R,hR,hv,hl.trans (congrArg (P.crossingPosition N D) hleft.symm),
      hr.trans (congrArg (P.crossingPosition N D) hright.symm)⟩
  · refine ⟨R.reverse,hR,hv,?_,?_⟩
    · exact R.reverse_source.trans (hr.trans (congrArg (P.crossingPosition N D) hleft.symm))
    · exact R.reverse_target.trans (hl.trans (congrArg (P.crossingPosition N D) hright.symm))

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPacketGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite bond packet represents a placed graph when its exact position
array and unordered edge support agree under a vertex permutation. -/

noncomputable section
namespace ContinuumCoulomb

structure QMAPacketGeometry (G : QMARationalExchangeGraph)
    (position : Fin G.n → ℕ × ℕ) (q : QuantumListPathStep.Output)
    (ps : List (ℕ × ℕ)) : Prop where
  bounded : SourceBondLists.bounded q.1 q.2.1
  noLoops : ∀ b ∈ q.2.1, b.1 ≠ b.2.1
  matching :
    let H := QuantumListGraph.ofBonds q.1 q.2.1 q.2.2 bounded noLoops
    ∃ vertex : Fin H.n ≃ Fin G.n,
      ps = List.ofFn (fun v => position (vertex v)) ∧
      (∀ e : H.Edge, ∃ f : G.Edge,
        s(vertex (H.left e),vertex (H.right e)) = s(G.left f,G.right f)) ∧
      (∀ f : G.Edge, ∃ e : H.Edge,
        s(vertex (H.left e),vertex (H.right e)) = s(G.left f,G.right f))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathRelabeling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of the route invariant between different finite edge orders.
This is used when the emitted list order differs from a set's chosen order. -/

noncomputable section
namespace ContinuumCoulomb

structure QMAPathRelabeling (S T : QMAPathSchedule) where
  vertex : Fin S.graph.n ≃ Fin T.graph.n
  edge : S.graph.Edge ≃ T.graph.Edge
  left : ∀ e, vertex (S.graph.left e)=T.graph.left (edge e)
  right : ∀ e, vertex (S.graph.right e)=T.graph.right (edge e)
  work : ∀ e, S.work e=T.work (edge e)

namespace QMAPathRelabeling
variable {S T : QMAPathSchedule} (E : QMAPathRelabeling S T)

theorem inverse_left (f : T.graph.Edge) :
    E.vertex.symm (T.graph.left f)=S.graph.left (E.edge.symm f) := by
  have h := congrArg E.vertex.symm (E.left (E.edge.symm f))
  simpa only [Equiv.symm_apply_apply,Equiv.apply_symm_apply] using h.symm

theorem inverse_right (f : T.graph.Edge) :
    E.vertex.symm (T.graph.right f)=S.graph.right (E.edge.symm f) := by
  have h := congrArg E.vertex.symm (E.right (E.edge.symm f))
  simpa only [Equiv.symm_apply_apply,Equiv.apply_symm_apply] using h.symm

theorem inverse_work (f : T.graph.Edge) : S.work (E.edge.symm f)=T.work f := by
  simpa only [Equiv.apply_symm_apply] using E.work (E.edge.symm f)

def transport {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding S Γ) : QMAPathEmbedding T Γ where
  position v := P.position (E.vertex.symm v)
  position_injective := P.position_injective.comp E.vertex.symm.injective
  point e k := P.point (E.edge.symm e) k
  first e := by rw [E.inverse_left]; exact P.first _
  last e := by rw [← E.inverse_work,E.inverse_right]; exact P.last _
  simple e i j hi hj h := by
    rw [← E.inverse_work] at hi hj
    exact P.simple _ i j hi hj h
  step e i hi := by
    rw [← E.inverse_work] at hi
    exact P.step _ i hi
  avoids e i v hi0 hi := by
    rw [← E.inverse_work] at hi
    exact P.avoids _ i _ hi0 hi
  disjoint e f i j hef hi0 hi hj := by
    rw [← E.inverse_work] at hi hj
    exact P.disjoint _ _ i j (fun h => hef (E.edge.symm.injective h)) hi0 hi hj

end QMAPathRelabeling
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathRelabelingProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree and inverse transport for finite relabelings of scheduled graphs. -/

noncomputable section
namespace ContinuumCoulomb.QMAPathRelabeling
open scoped BigOperators Classical

variable {S T : QMAPathSchedule} (E : QMAPathRelabeling S T)

def symm : QMAPathRelabeling T S where
  vertex := E.vertex.symm
  edge := E.edge.symm
  left := E.inverse_left
  right := E.inverse_right
  work f := (E.inverse_work f).symm

end ContinuumCoulomb.QMAPathRelabeling

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathRelabelingNext
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.mem_crossingCells _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relabeling commutes with a scheduled subdivision. This identifies the
literal list order with the physical port graph through every round. -/

noncomputable section
namespace ContinuumCoulomb.QMAPathRelabeling
open MediatorGraph
open scoped Classical
variable {S T : QMAPathSchedule} (E : QMAPathRelabeling S T)

def activeEquiv : {e // e ∈ S.active} ≃ {e // e ∈ T.active} :=
  Equiv.subtypeEquiv E.edge (by intro e; simp only [QMAPathSchedule.mem_active,E.work])
def retainedEquiv : {e // e ∉ S.active} ≃ {e // e ∉ T.active} :=
  Equiv.subtypeEquiv E.edge (by intro e; simp only [QMAPathSchedule.mem_active,E.work])
def activeIndex : Fin S.active.card ≃ Fin T.active.card :=
  (S.active.equivFin.symm.trans E.activeEquiv).trans T.active.equivFin

theorem selected_index (i : Fin S.active.card) :
    E.edge (qmaSelectedIndex S.active i)=qmaSelectedIndex T.active (E.activeIndex i) := by
  simp only [activeIndex,qmaSelectedIndex,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

def nextVertex : Fin (S.graph.n+S.active.card*2) ≃ Fin (T.graph.n+T.active.card*2) :=
  ((vertexEquiv _ _).symm.trans (Equiv.sumCongr E.vertex
    (Equiv.prodCongr E.activeIndex (Equiv.refl (Fin 2))))).trans (vertexEquiv _ _)
def nextEdge : QMAPartialPathsEdge S.active ≃ QMAPartialPathsEdge T.active :=
  Equiv.sumCongr E.retainedEquiv
    (Equiv.sumCongr E.activeIndex (Equiv.prodCongr E.activeIndex (Equiv.refl (Fin 2))))

theorem nextVertex_old (v : Fin S.graph.n) :
    E.nextVertex (old _ _ v)=old _ _ (E.vertex v) := by simp [nextVertex,old]
theorem nextVertex_fresh (i : Fin S.active.card) (a : Fin 2) :
    E.nextVertex (fresh _ _ i a)=fresh _ _ (E.activeIndex i) a := by
  simp [nextVertex,fresh]

theorem next_left (N : ℚ) (e : (S.next N).graph.Edge) :
    E.nextVertex ((S.next N).graph.left e)=(T.next N).graph.left (E.nextEdge e) := by
  rcases e with e | (i | ⟨i,a⟩)
  · change E.nextVertex (old _ _ (S.graph.left e.val))=old _ _ (T.graph.left (E.edge e.val))
    rw [E.nextVertex_old,E.left]
  · exact E.nextVertex_fresh i 0
  · fin_cases a
    · change E.nextVertex (old _ _ (S.graph.left (qmaSelectedIndex S.active i)))=
        old _ _ (T.graph.left (qmaSelectedIndex T.active (E.activeIndex i)))
      rw [E.nextVertex_old,E.left,E.selected_index]
    · change E.nextVertex (old _ _ (S.graph.right (qmaSelectedIndex S.active i)))=
        old _ _ (T.graph.right (qmaSelectedIndex T.active (E.activeIndex i)))
      rw [E.nextVertex_old,E.right,E.selected_index]

theorem next_right (N : ℚ) (e : (S.next N).graph.Edge) :
    E.nextVertex ((S.next N).graph.right e)=(T.next N).graph.right (E.nextEdge e) := by
  rcases e with e | (i | ⟨i,a⟩)
  · change E.nextVertex (old _ _ (S.graph.right e.val))=old _ _ (T.graph.right (E.edge e.val))
    rw [E.nextVertex_old,E.right]
  · exact E.nextVertex_fresh i 1
  · fin_cases a
    · exact E.nextVertex_fresh i 0
    · exact E.nextVertex_fresh i 1

theorem next_work (N : ℚ) (e : (S.next N).graph.Edge) :
    (S.next N).work e=(T.next N).work (E.nextEdge e) := by
  rcases e with e | (i | ⟨i,a⟩)
  · rfl
  · rfl
  · change (if a=1 then S.work (qmaSelectedIndex S.active i)-1 else 0)=
      (if a=1 then T.work (qmaSelectedIndex T.active (E.activeIndex i))-1 else 0)
    rw [E.work,E.selected_index]

def next (N : ℚ) : QMAPathRelabeling (S.next N) (T.next N) where
  vertex := E.nextVertex
  edge := E.nextEdge
  left := E.next_left N
  right := E.next_right N
  work := E.next_work N

end ContinuumCoulomb.QMAPathRelabeling

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPathRelabelingIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite route relabeling preserves the actual coordinates at every
scheduled subdivision round. -/

noncomputable section
namespace ContinuumCoulomb.QMAPathRelabeling
open MediatorGraph
open scoped Classical
variable {S T U : QMAPathSchedule}

def trans (E : QMAPathRelabeling S T) (F : QMAPathRelabeling T U) :
    QMAPathRelabeling S U where
  vertex := E.vertex.trans F.vertex
  edge := E.edge.trans F.edge
  left e := by simp only [Equiv.trans_apply,E.left,F.left]
  right e := by simp only [Equiv.trans_apply,E.right,F.right]
  work e := (E.work e).trans (F.work _)


end ContinuumCoulomb.QMAPathRelabeling

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingTableCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite table is the data of the actual port routes. Its membership
tests agree exactly with the permissions used in the geometric proof. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
open QuantumRoutingTable
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def routingVisits : List Visit :=
  (Finset.univ : Finset P.Interior).toList.flatMap (fun i =>
    [(P.cell i,((P.port i 0).val,(P.port i 1).val)),
     (P.cell i,((P.port i 1).val,(P.port i 0).val))])

def routingTable : Table :=
  (List.ofFn P.position,P.routingVisits,P.crossingCells.toList)

theorem routingTable_pair (p : ℕ × ℕ) (a b : Fin 4) :
    (p,(a.val,b.val)) ∈ P.routingTable.2.1 ↔
      ∃ i : P.Interior, P.cell i = p ∧ s(P.port i 0,P.port i 1) = s(a,b) := by
  change (p,(a.val,b.val)) ∈ P.routingVisits ↔ _
  simp only [routingVisits,List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and,
    List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq,Sym2.eq_iff]
  constructor
  · rintro ⟨i,⟨hc,ha,hb⟩ | ⟨hc,ha,hb⟩⟩
    · exact ⟨i,hc.symm,Or.inl ⟨(Fin.ext ha).symm,(Fin.ext hb).symm⟩⟩
    · exact ⟨i,hc.symm,Or.inr ⟨(Fin.ext hb).symm,(Fin.ext ha).symm⟩⟩
  · rintro ⟨i,hc,⟨ha,hb⟩ | ⟨ha,hb⟩⟩
    · exact ⟨i,Or.inl ⟨hc.symm,congrArg Fin.val ha.symm,congrArg Fin.val hb.symm⟩⟩
    · exact ⟨i,Or.inr ⟨hc.symm,congrArg Fin.val hb.symm,congrArg Fin.val ha.symm⟩⟩

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingCrossingTest
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

 theorem crossing_iff_opposite_visits (p : Pair) : P.IsCrossing p ↔
    (p,(0,2)) ∈ P.routingTable.2.1 ∧ (p,(1,3)) ∈ P.routingTable.2.1 := by
  have h02 := P.routingTable_pair p (0 : Fin 4) 2
  have h13 := P.routingTable_pair p (1 : Fin 4) 3
  change ((p,(0,2)) ∈ P.routingTable.2.1 ↔ _) at h02
  change ((p,(1,3)) ∈ P.routingTable.2.1 ↔ _) at h13
  rw [h02,h13]
  constructor
  · rintro ⟨i,j,hij,hi,hj,hpair⟩
    have h02 : s(0,2) ∈ P.pairing i j := by
      rw [hpair]
      simp [qmaCrossPortPairing]
    have h13 : s(1,3) ∈ P.pairing i j := by
      rw [hpair]
      simp [qmaCrossPortPairing]
    change s(0,2) ∈ ({s(P.port i 0,P.port i 1),s(P.port j 0,P.port j 1)} :
      Finset (Sym2 (Fin 4))) at h02
    change s(1,3) ∈ ({s(P.port i 0,P.port i 1),s(P.port j 0,P.port j 1)} :
      Finset (Sym2 (Fin 4))) at h13
    simp only [Finset.mem_insert,Finset.mem_singleton] at h02 h13
    rcases h02 with h02 | h02
    · refine ⟨⟨i,hi,h02.symm⟩,?_⟩
      rcases h13 with h13 | h13
      · exact False.elim ((by decide : (s(0,2) : Sym2 (Fin 4)) ≠ s(1,3))
          (h02.trans h13.symm))
      · exact ⟨j,hj,h13.symm⟩
    · refine ⟨⟨j,hj,h02.symm⟩,?_⟩
      rcases h13 with h13 | h13
      · exact ⟨i,hi,h13.symm⟩
      · exact False.elim ((by decide : (s(0,2) : Sym2 (Fin 4)) ≠ s(1,3))
          (h02.trans h13.symm))
  · rintro ⟨⟨i,hi,h02⟩,⟨j,hj,h13⟩⟩
    have hij : i ≠ j := by
      intro he
      subst j
      exact (by decide : (s(0,2) : Sym2 (Fin 4)) ≠ s(1,3)) (h02.symm.trans h13)
    refine ⟨i,j,hij,hi,hj,?_⟩
    change {s(P.port i 0,P.port i 1),s(P.port j 0,P.port j 1)} = _
    rw [h02,h13]
    rfl

end QMAPortRouteData
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

def lookup (xs : List Pair) (i : ℕ) : Pair := (xs.drop i).headD (0,0)

def visit (xs : List Pair) (i : ℕ) : Visit :=
  let p := lookup xs (i+1)
  (p,((qmaGridNeighborIndex p (lookup xs i)).val,
      (qmaGridNeighborIndex p (lookup xs (i+2))).val))

def both (v : Visit) : List Visit := [v,(v.1,v.2.swap)]

def visits (xs : List Pair) : List Visit :=
  ((List.range (xs.length-2)).map (fun i => both (visit xs i))).flatten

end ContinuumCoulomb.QuantumPathVisitProgram

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

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def routeList (e : G.Edge) : List Pair :=
  (List.range (P.length e+1)).map (P.point e)

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

def listedVisits (es : List G.Edge) : List Visit :=
  es.flatMap (fun e => visits (P.routeList e))

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPhysicalCells
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every physical spin retains the coarse cell of an original route point.
This transfers the original positive-coordinate and rectangle bounds. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical

@[simp] theorem qmaPointCell_inner (p : ℕ × ℕ) (a : Fin 4) :
    qmaPointCell (qmaInnerPort p a) = p := qmaInnerPort_cell p a

@[simp] theorem qmaPointCell_ancilla (p : ℕ × ℕ) (a : Fin 2) :
    qmaPointCell (qmaGadgetAncilla p a) = p := qmaGadgetAncilla_cell p a

theorem qmaCrossingMove_cell (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    {z : ℕ × ℕ} (hz : QMAPortPoint z) : qmaPointCell (qmaCrossingMove cross z) = qmaPointCell z := by
  rcases hz with ⟨p,rfl⟩ | ⟨p,a,rfl⟩
  · rw [qmaCrossingMove_center]
  · rw [qmaCrossingMove_port,qmaPointCell_port]
    split_ifs <;> simp only [qmaPointCell_inner,qmaPointCell_port]

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem chain_cell_property (Q : (ℕ × ℕ) → Prop)
    (hQ : ∀ e k, k ≤ P.length e → Q (P.point e k))
    (e : G.Edge) (k : ℕ) (hk : k ≤ 2*P.length e+1) :
    Q (qmaPointCell (qmaPortChain (P.point e) (P.length e) k)) := by
  by_cases h0 : k = 0
  · subst k
    simpa only [qmaPortChain_zero,qmaPointCell_center] using hQ e 0 (Nat.zero_le _)
  by_cases hlast : k = 2*P.length e+1
  · subst k
    simpa only [qmaPortChain_last,qmaPointCell_center] using hQ e (P.length e) le_rfl
  rw [qmaPortChain_inner (P.point e) (by omega) (by omega)]
  change Q (qmaPointCell (qmaGridPort (P.point e (k/2)) _))
  rw [qmaPointCell_port]
  exact hQ e (k/2) (by omega)

theorem finished_cell_property (Q : (ℕ × ℕ) → Prop)
    (hsource : ∀ v, Q (P.position v)) (hpath : ∀ e k, k ≤ P.length e → Q (P.point e k))
    (N : ℚ) (D : ℕ) (v : Fin (P.finishedGraph N D).n) : Q (qmaPointCell (P.finishedPosition N D v)) := by
  have h := P.toEmbedding.iterate_occupied_source N D (Or.inl ⟨v,rfl⟩)
  rcases h with ⟨w,hw⟩ | ⟨e,k,hk,he⟩
  · change qmaExpandedPoint (P.position w) = P.finishedPosition N D v at hw
    rw [← hw,qmaPointCell_center]
    exact hsource w
  · change qmaPortChain (P.point e) (P.length e) k = P.finishedPosition N D v at he
    rw [← he]
    exact P.chain_cell_property Q hpath e k hk

theorem crossingPosition_cell_property (Q : (ℕ × ℕ) → Prop)
    (hsource : ∀ v, Q (P.position v)) (hpath : ∀ e k, k ≤ P.length e → Q (P.point e k))
    (N : ℚ) (D : ℕ) (v : Fin ((P.finishedGraph N D).n+P.crossingCells.card*2)) :
    Q (qmaPointCell (P.crossingPosition N D v)) := by
  obtain ⟨v,rfl⟩ := (vertexEquiv (P.finishedGraph N D).n P.crossingCells.card).surjective v
  rcases v with v | ⟨i,a⟩
  · change Q (qmaPointCell (P.crossingPosition N D (old _ _ v)))
    rw [P.crossingPosition_old]
    change Q (qmaPointCell (qmaCrossingMove P.IsCrossing (P.finishedPosition N D v)))
    have hv : QMAPortPoint (P.finishedPosition N D v) := P.iterate_position_kind N D v
    rw [qmaCrossingMove_cell P.IsCrossing hv]
    exact P.finished_cell_property Q hsource hpath N D v
  · change Q (qmaPointCell (P.crossingPosition N D (fresh _ _ i a)))
    rw [P.crossingPosition_fresh]
    change Q (qmaPointCell (qmaGadgetAncilla (P.crossingCell i).val a))
    rw [qmaPointCell_ancilla]
    obtain ⟨j,k,hjk,hj,hk,hpair⟩ := P.mem_crossingCells.mp (P.crossingCell i).property
    rw [← hj]
    exact hpath j.1 (j.2.val+1) (P.cell_index_lt j).le

theorem crossingPosition_positive
    (hsource : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2)
    (N : ℚ) (D : ℕ) (v : Fin ((P.finishedGraph N D).n+P.crossingCells.card*2)) :
    0 < (qmaPointCell (P.crossingPosition N D v)).1 ∧
    0 < (qmaPointCell (P.crossingPosition N D v)).2 :=
  P.crossingPosition_cell_property (fun p => 0 < p.1 ∧ 0 < p.2) hsource P.positive N D v

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPlanarRouteData
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.mem_crossingCells _root_.OAI.ContinuumCoulomb.qmaFineRoute_nat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A planar route family supplies the even physical subdivision data explicitly,
including its four-direction reserved leaf sites. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

structure QMAPlanarRouteData (G : QMARationalExchangeGraph) where
  length : G.Edge → ℕ
  length_pos : ∀ e, 0 < length e
  position : Fin G.n → ℕ × ℕ
  position_injective : Function.Injective position
  point : G.Edge → ℕ → ℕ × ℕ
  positive : ∀ e i, i ≤ length e → 0 < (point e i).1 ∧ 0 < (point e i).2
  first : ∀ e, point e 0 = position (G.left e)
  last : ∀ e, point e (length e) = position (G.right e)
  simple : ∀ e i j, i ≤ length e → j ≤ length e → point e i = point e j → i = j
  step : ∀ e i, i < length e → qmaSquareGrid.Adj (point e i) (point e (i+1))
  avoids : ∀ e i v, 0 < i → i < length e → point e i ≠ position v
  disjoint : ∀ e f i j, e ≠ f → 0 < i → i < length e → j ≤ length f → point e i ≠ point f j
  edges_disjoint : ∀ e f, e ≠ f → ∀ i j, i < length e → j < length f →
    ¬(point e i = point f j ∧ point e (i+1) = point f (j+1)) ∧
    ¬(point e i = point f (j+1) ∧ point e (i+1) = point f j)

namespace QMAPlanarRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPlanarRouteData G)

def direction (e : G.Edge) : Fin 4 := qmaGridNeighborIndex (P.point e 0) (P.point e 1)

theorem direction_spec (e : G.Edge) :
    qmaGridNeighbor (P.point e 0) (P.direction e) = P.point e 1 :=
  qmaGridNeighborIndex_spec (P.positive e 0 (Nat.zero_le _)).1
    (P.positive e 0 (Nat.zero_le _)).2 (P.step e 0 (P.length_pos e))

def leaf (e : G.Edge) : ℕ × ℕ := qmaRouteLeaf (P.point e 0) (P.direction e)

theorem leaf_injective : Function.Injective P.leaf := by
  intro e f h
  by_contra hef
  have hp : (P.point e 0,P.direction e) = (P.point f 0,P.direction f) :=
    qmaRouteLeaf_injective h
  have h0 := congrArg Prod.fst hp
  have h1 := congrArg (fun z : (ℕ × ℕ) × Fin 4 => qmaGridNeighbor z.1 z.2) hp
  rw [P.direction_spec e,P.direction_spec f] at h1
  exact (P.edges_disjoint e f hef 0 0 (P.length_pos e) (P.length_pos f)).1 ⟨h0,h1⟩

theorem even_length (e : G.Edge) : 2*(4*P.length e-1)+2 = 8*P.length e := by
  have h := P.length_pos e
  omega

def toEven : QMAEvenRouteData G where
  work e := 4*P.length e-1
  position v := qmaLeafCenter (P.position v)
  position_injective := qmaLeafCenter_injective.comp P.position_injective
  point e := qmaInflatedPoint (P.point e)
  first e := by rw [qmaInflatedPoint_zero,P.first]
  last e := by rw [P.even_length,qmaInflatedPoint_last,P.last]
  simple e i j hi hj h := by
    rw [P.even_length] at hi hj
    exact qmaInflatedPoint_injective (P.point e) (P.positive e) (P.step e) (P.simple e) hi hj h
  step e i hi := by
    rw [P.even_length] at hi
    exact qmaInflatedPoint_step (P.point e) (P.step e) hi
  avoids e i v hi0 hi := by
    rw [P.even_length] at hi
    exact qmaInflatedPoint_avoids_vertex (P.point e) (P.positive e) (P.step e) (P.position v)
      (fun j hj0 hj => P.avoids e j v hj0 hj) hi0 hi
  disjoint e f i j hef hi0 hi hj := by
    rw [P.even_length] at hi
    rw [P.even_length] at hj
    exact qmaInflatedPoint_disjoint (P.point e) (P.point f) (P.positive e) (P.positive f)
      (P.step e) (P.step f) (fun a b ha0 ha hb => P.disjoint e f a b hef ha0 ha hb)
      (P.edges_disjoint e f hef) hi0 hi hj
  leaf := P.leaf
  leaf_injective := P.leaf_injective
  leaf_step e := by
    change qmaSquareGrid.Adj
      (qmaManhattanPoint (qmaLeafCenter (P.point e 0)) (qmaLeafCenter (P.point e 1)) 1) (P.leaf e)
    rw [qmaLeafCenter_point_first (P.positive e 0 (Nat.zero_le _)).1
      (P.positive e 0 (Nat.zero_le _)).2 (P.step e 0 (P.length_pos e))]
    exact qmaRouteLeaf_step _ _
  leaf_avoids e f k hk := by
    rw [P.even_length] at hk
    exact qmaRouteLeaf_avoids _ _ _ (qmaInflatedPoint_gridline (P.point f) (P.step f) hk)
  leaf_old e v := by
    apply qmaRouteLeaf_avoids
    left
    simp [qmaLeafCenter,Nat.add_mod]

end QMAPlanarRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPlanarListData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the concrete finite cell paths to the coordinate-array interface used
by the fixed-round physical subdivision theorem. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

structure QMAPlanarListData (G : QMARationalExchangeGraph) where
  position : Fin G.n → ℕ × ℕ
  position_injective : Function.Injective position
  path : G.Edge → List (ℕ × ℕ)
  length : ∀ e, 3 ≤ (path e).length
  first : ∀ e, (path e).head? = some (position (G.left e))
  last : ∀ e, (path e).getLast? = some (position (G.right e))
  simple : ∀ e, (path e).Nodup
  step : ∀ e, (path e).IsChain (fun p q => qmaSquareGrid.Adj p q)
  positive : ∀ e p, p ∈ path e → 0 < p.1 ∧ 0 < p.2
  avoids : ∀ e v, position v ∉ ((path e).drop 1).dropLast
  disjoint : ∀ e f, e ≠ f →
    Disjoint (((path e).drop 1).dropLast).toFinset (path f).toFinset

namespace QMAPlanarListData
variable {G : QMARationalExchangeGraph} (P : QMAPlanarListData G)

def point (e : G.Edge) (k : ℕ) : ℕ × ℕ := (P.path e).getD k (0,0)

theorem point_get (e : G.Edge) {k : ℕ} (hk : k < (P.path e).length) :
    P.point e k = (P.path e)[k] := List.getD_eq_getElem _ _ hk

theorem point_mem (e : G.Edge) {k : ℕ} (hk : k < (P.path e).length) :
    P.point e k ∈ P.path e := by
  rw [P.point_get e hk]
  exact List.getElem_mem _

theorem point_interior (e : G.Edge) {k : ℕ} (hk0 : 0 < k) (hk : k < (P.path e).length-1) :
    P.point e k ∈ ((P.path e).drop 1).dropLast := by
  have hi : k-1 < (((P.path e).drop 1).dropLast).length := by
    simp only [List.length_dropLast,List.length_drop]
    omega
  have hm := List.getElem_mem (l := ((P.path e).drop 1).dropLast) hi
  rw [List.getElem_dropLast,List.getElem_drop] at hm
  simpa only [show 1+(k-1) = k from by omega,← P.point_get e (k := k) (by omega)] using hm

theorem point_disjoint (e f : G.Edge) (hef : e ≠ f) {i j : ℕ}
    (hi0 : 0 < i) (hi : i < (P.path e).length-1) (hj : j < (P.path f).length) :
    P.point e i ≠ P.point f j := by
  intro h
  have he := P.point_interior e hi0 hi
  rw [h] at he
  exact Finset.disjoint_left.mp (P.disjoint e f hef) (List.mem_toFinset.mpr he)
    (List.mem_toFinset.mpr (P.point_mem f hj))

def toRoute : QMAPlanarRouteData G where
  length e := (P.path e).length-1
  length_pos e := by have := P.length e; omega
  position := P.position
  position_injective := P.position_injective
  point := P.point
  positive e k hk := P.positive e _ (P.point_mem e (by have := P.length e; omega))
  first e := by
    have h := P.first e
    rw [List.head?_eq_getElem?,List.getElem?_eq_getElem (by have := P.length e; omega)] at h
    exact (P.point_get e (by have := P.length e; omega)).trans (Option.some.inj h)
  last e := by
    have h := P.last e
    rw [List.getLast?_eq_getElem?,List.getElem?_eq_getElem (by have := P.length e; omega)] at h
    exact (P.point_get e (by have := P.length e; omega)).trans (Option.some.inj h)
  simple e i j hi hj h := by
    have hi' : i < (P.path e).length := by have := P.length e; omega
    have hj' : j < (P.path e).length := by have := P.length e; omega
    rw [P.point_get e hi',P.point_get e hj'] at h
    exact (P.simple e).getElem_inj_iff.mp h
  step e i hi := by
    rw [P.point_get e (by omega),P.point_get e (by omega)]
    exact List.isChain_iff_getElem.mp (P.step e) i (by omega)
  avoids e i v hi0 hi := by
    intro h
    exact P.avoids e v (h ▸ P.point_interior e hi0 hi)
  disjoint e f i j hef hi0 hi hj :=
    P.point_disjoint e f hef hi0 hi (by have := P.length f; omega)
  edges_disjoint e f hef i j hi hj := by
    have hi' : i+1 < (P.path e).length := by omega
    have hj' : j+1 < (P.path f).length := by omega
    constructor
    · rintro ⟨h0,h1⟩
      by_cases h : i = 0
      · subst i
        exact P.point_disjoint e f hef (by omega) (by have := P.length e; omega) hj' h1
      · exact P.point_disjoint e f hef (by omega) hi (by omega) h0
    · rintro ⟨h0,h1⟩
      by_cases h : i = 0
      · subst i
        exact P.point_disjoint e f hef (by omega) (by have := P.length e; omega) (by omega) h1
      · exact P.point_disjoint e f hef (by omega) hi hj' h0

end QMAPlanarListData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPlanarRouteRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded planar route family produces the actual nearest-neighbor rational
Hamiltonian with a fixed number of perturbative layers. -/

namespace ContinuumCoulomb

noncomputable section
open scoped Classical
namespace QMAPlanarRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPlanarRouteData G)

def Bounded (X Y : ℕ) : Prop :=
  (∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y) ∧
  ∀ e i, i ≤ P.length e → (P.point e i).1 < X ∧ (P.point e i).2 < Y

end QMAPlanarRouteData
end
end ContinuumCoulomb

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
open QuantumFiniteRouteSearch

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def HasAllowedRoute (x y : ℕ × ℕ) : Prop :=
  ∃ R : QMACellRoute, P.RoutingAllowed R.body ∧ R.Valid ∧ R.source = x ∧ R.target = y

def findAllowedRoute (x y : ℕ × ℕ) : Option QMACellRoute :=
  (qmaRouteCandidates x y).find? (fun R =>
    decide (P.RoutingAllowed R.body ∧ R.Valid ∧ R.source = x ∧ R.target = y))

theorem findAllowedRoute_isSome {x y : ℕ × ℕ} (h : P.HasAllowedRoute x y) :
    (P.findAllowedRoute x y).isSome := by
  obtain ⟨R,ha,hv,hs,ht⟩ := h
  apply List.find?_isSome.mpr
  refine ⟨R,?_,decide_eq_true ⟨ha,hv,hs,ht⟩⟩
  simpa only [hs,ht] using qmaRouteCandidates_complete R

theorem hasAllowedRoute_reverse {x y : ℕ × ℕ} (h : P.HasAllowedRoute x y) :
    P.HasAllowedRoute y x := by
  obtain ⟨R,ha,hv,hs,ht⟩ := h
  exact ⟨R.reverse,ha,hv,R.reverse_source.trans ht,R.reverse_target.trans hs⟩

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

theorem crossing_hasAllowedRoute (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (x y : Fin (P.crossingOutput N hD).merge.n)
    (e : (P.crossingOutput N hD).merge.Edge)
    (he : s(x,y) = s((P.crossingOutput N hD).merge.left e,
      (P.crossingOutput N hD).merge.right e)) :
    P.HasAllowedRoute (P.crossingPosition N D x) (P.crossingPosition N D y) := by
  have h : P.HasAllowedRoute
      (P.crossingPosition N D ((P.crossingOutput N hD).merge.left e))
      (P.crossingPosition N D ((P.crossingOutput N hD).merge.right e)) :=
    P.mergedOutput_route_exists N hD havoid e
  rcases Sym2.eq_iff.mp he with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · simpa only [hl,hr] using h
  · simpa only [hl,hr] using P.hasAllowedRoute_reverse h

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortSelectionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The endpoint scan uses the exact canonical crossing couplings of the
completed physical port graph. Disjoint terminal sets discharge uniqueness. -/

noncomputable section
namespace ContinuumCoulomb.QMAPortRouteData
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem crossingSiteFin_global (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) :
    Function.Injective (fun p : Fin P.crossingCells.card × Fin 4 =>
      P.crossingSiteFin N hD p.1 p.2) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have hp : (P.crossingCell i,qmaPatchDirection a)=(P.crossingCell j,qmaPatchDirection b) :=
    P.crossingSite_injective N hD h
  have hi : P.crossingCell i=P.crossingCell j :=
    congrArg (fun x : P.Crossing × Fin 4 => x.1) hp
  have hij : i=j := P.crossingCells.equivFin.symm.injective hi
  have hab : a=b := qmaPatchDirection_injective
    (congrArg (fun x : P.Crossing × Fin 4 => x.2) hp)
  exact Prod.ext hij hab

end ContinuumCoulomb.QMAPortRouteData

end

end OAI
end


