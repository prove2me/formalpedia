-- Prove2me | Definitions.Def_OAIQ244Duke012
-- name    : OAIQ244Duke012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:12:37.217525+00:00
-- url     : https://prove2.me/theorems/92eba25b-8c4c-4d4d-9ce9-d9429d546b5a
-- title:
--   Definitions bundle OAIQ244Duke012 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 464 declarations of OpenAI's Lean: 271 definitions, 1 inductive type or structure, 16 instances and 176 theorems. The definitions and types are `OAI.DukePrimeDegree.MatrixEuclidean`, `OAI.DukePrimeDegree.RootTransverseRectangle`, `OAI.DukePrimeDegree.RootTransverseRectangle.inclusion`, `OAI.DukePrimeDegree.UniformFinitePredecessors`, `OAI.DukePrimeDegree.badOrbitFiberMass`, `OAI.DukePrimeDegree.blockComplementSetoid`, `OAI.DukePrimeDegree.blockLowerEntries`, `OAI.DukePrimeDegree.blockOffDiagonalEntries`, `OAI.DukePrimeDegree.blockProjection`, `OAI.DukePrimeDegree.blockScalarAlgHom`, `OAI.DukePrimeDegree.blockScalarAlgebra`, `OAI.DukePrimeDegree.blockUpperEntries`, `OAI.DukePrimeDegree.boundedAbsCoordinate`, `OAI.DukePrimeDegree.centralizerWitnessWeights`, `OAI.DukePrimeDegree.columnIsolatingRaw`, `OAI.DukePrimeDegree.commutatorFamily`, `OAI.DukePrimeDegree.compactObservableTranslate`, `OAI.DukePrimeDegree.conditionalInformation`, `OAI.DukePrimeDegree.conjugateLinearCharacter`, `OAI.DukePrimeDegree.constantL2`, `OAI.DukePrimeDegree.countableFutureCode`, `OAI.DukePrimeDegree.countableFutureFiber`, `OAI.DukePrimeDegree.cyclicZeroSign`, `OAI.DukePrimeDegree.degreePred`, `OAI.DukePrimeDegree.dyadicBoundaryCost`, `OAI.DukePrimeDegree.entireFutureObservation`, `OAI.DukePrimeDegree.excessiveOccupation`, `OAI.DukePrimeDegree.finiteCutCode`, `OAI.DukePrimeDegree.finiteFrameVector`, `OAI.DukePrimeDegree.finiteLabelLift`, `OAI.DukePrimeDegree.finiteOrbitNeighbor`, `OAI.DukePrimeDegree.firstCoordinateSlice`, `OAI.DukePrimeDegree.firstCoverCode`, `OAI.DukePrimeDegree.firstTrue`, `OAI.DukePrimeDegree.frameEnumeration`, `OAI.DukePrimeDegree.frameMinor`, `OAI.DukePrimeDegree.fullFutureSigma`, `OAI.DukePrimeDegree.futureLabelBlock`, `OAI.DukePrimeDegree.heightBoundary`, `OAI.DukePrimeDegree.heightClip` and 232 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `DukePrimeDegree_Arithmetic_ConjugateSubfields`, `DukePrimeDegree_Arithmetic_CyclicContinuation`, `DukePrimeDegree_Arithmetic_CyclicGluing`, `DukePrimeDegree_Arithmetic_CyclicIntegerOrders`, `DukePrimeDegree_Arithmetic_CyclicRealCharacters`, `DukePrimeDegree_Arithmetic_CyclicSubfields`, `DukePrimeDegree_Arithmetic_PermutationEuler`, `DukePrimeDegree_Arithmetic_StarkAverage`, `DukePrimeDegree_Arithmetic_StarkCharacters`, `DukePrimeDegree_Arithmetic_StarkDescent`, `DukePrimeDegree_Arithmetic_SubfieldOrders`, `DukePrimeDegree_Arithmetic_ZeroPropagation`, `DukePrimeDegree_Arithmetic_ZetaOrder`, `DukePrimeDegree_Dynamics_BlockDiagonalAlgebra`, `DukePrimeDegree_Dynamics_BlockEliminationSchedule`, `DukePrimeDegree_Dynamics_BlockNormalizer`, `DukePrimeDegree_Dynamics_CentralizerWeights`, `DukePrimeDegree_Dynamics_CompactFamilyGeneric`, `DukePrimeDegree_Dynamics_DiagonalRecurrence`, `DukePrimeDegree_Dynamics_ErgodicAverageMean`, `DukePrimeDegree_Dynamics_EuclideanVelocityProjection`, `DukePrimeDegree_Dynamics_ExactInvariantFunctions`, `DukePrimeDegree_Dynamics_FlowOccupation`, `DukePrimeDegree_Dynamics_FlowSmoothedL2`, `DukePrimeDegree_Dynamics_FlowWindowAverages`, `DukePrimeDegree_Dynamics_HopfMaximal`, `DukePrimeDegree_Dynamics_HorosphereIsolatingFlow`, `DukePrimeDegree_Dynamics_IntegrableCoboundary`, `DukePrimeDegree_Dynamics_LeafFlowCovariance`, `DukePrimeDegree_Dynamics_MautnerLatticeL2`, `DukePrimeDegree_Dynamics_MaximalOccupation`, `DukePrimeDegree_Dynamics_OrbitCoboundary`, `DukePrimeDegree_Dynamics_PrimeBlockRationality`, `DukePrimeDegree_Dynamics_RationalCentralizer`, `DukePrimeDegree_Dynamics_ScalarOrbitCommutant`, `DukePrimeDegree_Dynamics_SeparatedOrbitCover`, `DukePrimeDegree_Dynamics_ShearingDiagonal`, `DukePrimeDegree_Dynamics_SingleBlockNormalization`, `DukePrimeDegree_Dynamics_SingleBlockTransverse`, `DukePrimeDegree_Dynamics_SmallCentralizer`, `DukePrimeDegree_Dynamics_TranslationInvariantProduct`, `DukePrimeDegree_Dynamics_TranslationInvariantSlices`, `DukePrimeDegree_Dynamics_WeylAtomicRoots`, `DukePrimeDegree_Entropy_BilateralFiniteCodes`, `DukePrimeDegree_Entropy_ConditionalInformation`, `DukePrimeDegree_Entropy_ConditioningFiniteLabels`, `DukePrimeDegree_Entropy_CountableFutureCodes`, `DukePrimeDegree_Entropy_CountableFutureMap`, `DukePrimeDegree_Entropy_CountableFutureSigma`, `DukePrimeDegree_Entropy_EntropyInverse`, `DukePrimeDegree_Entropy_FutureLabelBlocks`, `DukePrimeDegree_Entropy_FutureSigmaAlgebra`, `DukePrimeDegree_Entropy_HeightObservationEntropy`, `DukePrimeDegree_Entropy_LastActiveObservation`, `DukePrimeDegree_Entropy_LayeredObservations`, `DukePrimeDegree_Entropy_LayeredPredecessors`, `DukePrimeDegree_Entropy_ObservationInformation`, `DukePrimeDegree_Entropy_PeriodicEntropyZero`, `DukePrimeDegree_Entropy_PredecessorWholeFutureSigma`, `DukePrimeDegree_Entropy_RareLabelEntropy`, `DukePrimeDegree_Entropy_RareTernaryEntropy`, `DukePrimeDegree_Entropy_SummablePartitionBoundaries`, `DukePrimeDegree_Entropy_WeylEntropy`, `DukePrimeDegree_Geometry_CutFamilyCode`, `DukePrimeDegree_Geometry_DiracFiberGraph`, `DukePrimeDegree_Geometry_DyadicBoundaryCuts`, `DukePrimeDegree_Geometry_FiniteProjectionFrames`, `DukePrimeDegree_Geometry_FirstCoverCode`, `DukePrimeDegree_Geometry_FrameWeightRigidity`, `DukePrimeDegree_Geometry_GoodSetFiberCorrection`, `DukePrimeDegree_Geometry_HeightBoundaryCount`, `DukePrimeDegree_Geometry_LocalQuotientPacking`, `DukePrimeDegree_Geometry_MatrixConjugationDensity`, `DukePrimeDegree_Geometry_MatrixCoordinateFrames`, `DukePrimeDegree_Geometry_NeutralTransverseCoordinates`, `DukePrimeDegree_Geometry_NeutralWeightSpace`, `DukePrimeDegree_Geometry_NormalizedFrame`, `DukePrimeDegree_Geometry_OpenRegionEmbedding`, `DukePrimeDegree_Geometry_PairedCoordinateAlgebra`, `DukePrimeDegree_Geometry_PluckerCovariance`, `DukePrimeDegree_Geometry_QuantitativeDistanceNet`, `DukePrimeDegree_Geometry_RootCurveExtraction`, `DukePrimeDegree_Geometry_RootFactorTransversal`, `DukePrimeDegree_Geometry_RootTransverseRectangles`, `DukePrimeDegree_Geometry_ShiftedRootPullback`, `DukePrimeDegree_Geometry_SpectralSeparation`, `DukePrimeDegree_Geometry_WeylReindex`, `PrimePackets_AnalyticLogarithms`, `PrimePackets_ArtinEuler`, `PrimePackets_ArtinSeries`, `PrimePackets_AtomMass`, `PrimePackets_ConditionalFibers`, `PrimePackets_CongruenceLattices`, `PrimePackets_CoordinateLattices`, `PrimePackets_CosetMeromorphic`, `PrimePackets_CuspMass`, `PrimePackets_DivisorBounds`, `PrimePackets_EntropyMixtures`, `PrimePackets_FrobeniusCoset`, `PrimePackets_FunctionalEquation`, `PrimePackets_GaussianMellin`, `PrimePackets_HaarBounds`, `PrimePackets_HaarUniqueness`, `PrimePackets_IdealClasses`, `PrimePackets_IdealCoefficients`, `PrimePackets_IdealNorms`, `PrimePackets_IdealSupport`, `PrimePackets_IdealThetaXi`, `PrimePackets_IntegerEmbeddings`, `PrimePackets_IntervalSieve`, `PrimePackets_IntrinsicLeaves`, `PrimePackets_InverseEntropy`, `PrimePackets_KernelEntropy`, `PrimePackets_KernelScaling`, `PrimePackets_LeafAnchors`, `PrimePackets_LeafNormalization`, `PrimePackets_LeafPeriods`, `PrimePackets_LeafSupport`, `PrimePackets_LocalEuler`, `PrimePackets_LocalModels`, `PrimePackets_LocalMoments`, `PrimePackets_MangoldtBounds`, `PrimePackets_MellinGrowth`, `PrimePackets_NormalClosure`, `PrimePackets_ObservationConditionalProbability`, `PrimePackets_ObservationSigmaAlgebra`, `PrimePackets_OrbitProbability`, `PrimePackets_PacketAlgebra`, `PrimePackets_PenaltyEuler`, `PrimePackets_PeriodicTheta`, `PrimePackets_PermutationArtin`, `PrimePackets_PowerfulIdeals`, `PrimePackets_PrimeFactors`, `PrimePackets_PrimeSums`, `PrimePackets_PrincipalUnits`, `PrimePackets_RadialIntegrals`, `PrimePackets_RayCharacter`, `PrimePackets_RayUnramified`, `PrimePackets_RootCharts`, `PrimePackets_RootInvariance`, `PrimePackets_RootLeaves`, `PrimePackets_RootOverlaps`, `PrimePackets_RootRelations`, `PrimePackets_ScalingCovariance`, `PrimePackets_SieveConvolution`, `PrimePackets_SplitEuler`, `PrimePackets_SubquadraticGrowth`, `PrimePackets_ThetaReflection`, `PrimePackets_ThetaTails`, `PrimePackets_XiBoundary`, `PrimePackets_ZeroReflection`, `PrimePackets_ZetaDerivatives`, `PrimePackets_ZetaResidues`.
--
--   **Imports.** It imports the published bundle `Def_DukePrimeDegree`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke020`, `OAIQ244Duke022`, `OAIQ244Duke023` and `OAIQ244Duke024`; the statements `OAI.DukePrimeDegree.exists_bounded_cover_subordinate_observation`, `OAI.DukePrimeDegree.logRegularized_deriv_bound_of_completedXi_gap`, `OAI.PrimeDegreePackets.AnalyticGrowth.hasSum_realZeroPole`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_hasSubquadraticGrowth`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_logDeriv_base_le_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.dedekindXi_realZeroPole_nonneg_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.idealThetaXi_reflection_totallyReal` and `OAI.PrimeDegreePackets.coprime_ideal_scaled_interval`; the proof of `OAI.PrimeDegreePackets.AnalyticGrowth.hasSum_realZeroPole`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Pairing
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Flat.IsBaseChange
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_HaarBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal

open IsDiscreteValuationRing IsLocalRing
namespace PrimeDegreePackets

lemma mem_maximalIdeal_pow_iff_addVal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (x : R) (k : ℕ) :
    x ∈ IsLocalRing.maximalIdeal R ^ k ↔ (k : ℕ∞) ≤ addVal R x := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← addVal_le_iff_dvd, hπ.addVal_pow]



end PrimeDegreePackets


open scoped ENNReal BigOperators
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalMoments
attribute [-instance] _root_.OAI.PrimeDegreePackets.xMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators


namespace PrimeDegreePackets


section
variable {R A : Type*} [Ring R] [AddCommGroup A] [Module R A]
    [MeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (L : Submodule R A) [Finite (A ⧸ L)]

 
def normalizedSubmoduleHaar : Measure L :=
  (L.cardQuot : ℝ≥0∞) • μ.comap ((↑) : L → A)

end
end PrimeDegreePackets


open MeasureTheory Set IsDiscreteValuationRing


namespace PrimeDegreePackets

section Algebra
variable {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)]
    [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]

 
def productDVRShell (k : ι → ℕ) : Set (∀ i, R i) :=
  {x | ∀ i, addVal (R i) (x i) = k i}

lemma productDVRShell_nonempty (k : ι → ℕ) : (productDVRShell R k).Nonempty := by
  choose π hπ using (fun i => exists_irreducible (R i))
  exact ⟨fun i => π i ^ k i, fun i => (hπ i).addVal_pow _⟩

end Algebra

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators
section
variable {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]

def shellNorm (k : ι → ℕ) : ℝ≥0∞ :=
  ∏ i, (Nat.card (IsLocalRing.ResidueField (R i)) : ℝ≥0∞) ^ k i

def localZinv : ℝ≥0∞ :=
  ∏ i, (1 - (Nat.card (IsLocalRing.ResidueField (R i)) : ℝ≥0∞)⁻¹)

end
end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module

universe u
open scoped TensorProduct
open Set Module
namespace PrimeDegreePackets

lemma prime_coprime_other_factors {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ j, Fact (p j).Prime] (hp : Function.Injective p) (k : ι → ℕ) (j : ι) :
    Nat.Coprime (p j) (∏ i ∈ Finset.univ.erase j, (p i)^(k i)) := by
  apply Nat.Coprime.prod_right
  intro i hi
  apply Nat.Coprime.pow_right
  exact (Nat.coprime_primes (Fact.out : (p j).Prime) (Fact.out : (p i).Prime)).mpr
    (hp.ne (Finset.ne_of_mem_erase hi).symm)



lemma rat_integral_of_padic_integral (q : ℚ)
    (h : ∀ (p : ℕ) (hp : p.Prime), let : Fact p.Prime := ⟨hp⟩;
      ‖(q : Padic p)‖ ≤ 1) : ∃ z : ℤ, (z : ℚ) = q := by
  suffices hd : q.den = 1 from ⟨q.num, (Rat.den_eq_one_iff q).mp hd⟩
  by_contra hd
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
  let : Fact p.Prime := ⟨hp⟩
  have hdn : (q.den : Padic p) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have hdlt : ‖(q.den : Padic p)‖ < 1 := Padic.norm_natCast_lt_one_iff.mpr hpd
  have hn : ‖(q.num : Padic p)‖ = 1 := by
    rw [← norm_natAbs]
    exact Padic.norm_natCast_eq_one_iff.mpr (q.reduced.coprime_dvd_right hpd).symm
  have hq := h p hp
  change ‖(q : Padic p)‖ ≤ 1 at hq
  rw [Rat.cast_def, norm_div, hn] at hq
  have := (one_lt_div (norm_pos_iff.mpr hdn)).mpr hdlt
  exact (not_lt_of_ge hq) this


open scoped NumberField Pointwise nonZeroDivisors
open NumberField


open Topology
open scoped Pointwise

open Polynomial

 

theorem isIntegral_padicInt_iff_spectralNorm_le_one
    (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] [Algebra (Padic p) E]
    [FiniteDimensional (Padic p) E] [Algebra (PadicInt p) E]
    [IsScalarTower (PadicInt p) (Padic p) E] (x : E) :
    IsIntegral (PadicInt p) x ↔ spectralNorm (Padic p) E x ≤ 1 := by
  constructor
  · rintro ⟨f,hf,hfx⟩
    have hf' : (f.map (algebraMap (PadicInt p) (Padic p))).Monic := hf.map _
    have hr : aeval x (f.map (algebraMap (PadicInt p) (Padic p))) = 0 := by
      rw [aeval_map_algebraMap,aeval_def]
      exact hfx
    have hle : spectralValue (f.map (algebraMap (PadicInt p) (Padic p))) ≤ 1 := by
      apply (spectralValue_le_one_iff hf').mpr
      intro i
      rw [coeff_map]
      exact (f.coeff i).property
    exact (norm_root_le_spectralValue (f := spectralAlgNorm (Padic p) E)
      (spectralAlgNorm_isPowMul (K := Padic p) (L := E)) (isNonarchimedean_spectralNorm (K := Padic p) (L := E))
      hf' hr).trans hle
  · intro hx
    let f := minpoly (Padic p) x
    have hf : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
    have hcoeff : ∀ i : ℕ, ‖f.coeff i‖ ≤ 1 := (spectralValue_le_one_iff hf).mp hx
    let g : (PadicInt p)[X] := ∑ i ∈ f.support, monomial i (⟨f.coeff i,hcoeff i⟩ : PadicInt p)
    have hg : g.map (algebraMap (PadicInt p) (Padic p)) = f := by
      dsimp only [g]
      rw [Polynomial.map_sum]
      calc
        _ = ∑ i ∈ f.support, monomial i (f.coeff i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Polynomial.map_monomial (algebraMap (PadicInt p) (Padic p))
        _ = f := sum_monomial_eq f
    have hgm : g.Monic := Polynomial.monic_of_injective
      (FaithfulSMul.algebraMap_injective (PadicInt p) (Padic p)) (hg.symm ▸ hf)
    refine ⟨g,hgm,?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap (Padic p),hg]
    exact minpoly.aeval (Padic p) x

open scoped NNReal
section NormedIntegers
variable (E : Type*) [NontriviallyNormedField E] [IsUltrametricDist E]
local instance instValuedNNReal_solutions : Valued E ℝ≥0 := NormedField.toValued

lemma compactSpace_norm_integer [ProperSpace E] : CompactSpace (Valued.integer E) := by
  apply isCompact_iff_compactSpace.mp
  change IsCompact {x : E | ‖x‖₊ ≤ 1}
  convert isCompact_closedBall (0 : E) 1 using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [Metric.mem_closedBall,dist_zero_right,Set.mem_ofPred_eq]
  exact NNReal.coe_le_coe

lemma dvr_norm_integer [ProperSpace E] : IsDiscreteValuationRing (Valued.integer E) := by
  let : CompactSpace (Valued.integer E) := compactSpace_norm_integer E
  let : (Valued.v (R := E) (Γ₀ := ℝ≥0)).IsNontrivial :=
    inferInstanceAs (NormedField.valuation (K := E)).IsNontrivial
  exact Valued.integer.isDiscreteValuationRing_of_compactSpace

lemma finite_residue_norm_integer [ProperSpace E] :
    Finite (IsLocalRing.ResidueField (Valued.integer E)) := by
  let : CompactSpace (Valued.integer E) := compactSpace_norm_integer E
  let : (Valued.v (R := E) (Γ₀ := ℝ≥0)).RankOne :=
    inferInstanceAs (NormedField.valuation (K := E)).RankOne
  exact (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    inferInstance).2.2

variable (p : ℕ) [Fact p.Prime] [NormedAlgebra (Padic p) E]
    [FiniteDimensional (Padic p) E] [Algebra (PadicInt p) E]
    [IsScalarTower (PadicInt p) (Padic p) E]

 
def integralClosureEquivInteger :
    integralClosure (PadicInt p) E ≃+* Valued.integer E :=
  RingEquiv.subringCongr (show (integralClosure (PadicInt p) E).toSubring =
      Valued.integer E from by
    ext x
    change IsIntegral (PadicInt p) x ↔ ‖x‖₊ ≤ 1
    rw [isIntegral_padicInt_iff_spectralNorm_le_one p E,
      ← NormedAlgebra.norm_eq_spectralNorm (Padic p)]
    exact_mod_cast (NNReal.coe_le_coe :
      (‖x‖₊ : ℝ) ≤ ((1 : ℝ≥0) : ℝ) ↔ ‖x‖₊ ≤ 1))

lemma compactSpace_integralClosure_padic [ProperSpace E] :
    CompactSpace (integralClosure (PadicInt p) E) := by
  apply isCompact_iff_compactSpace.mp
  change IsCompact {x : E | IsIntegral (PadicInt p) x}
  have heq : {x : E | IsIntegral (PadicInt p) x} = Metric.closedBall 0 1 := by
    ext x
    simp only [Set.mem_ofPred_eq,Metric.mem_closedBall,dist_zero_right,
      isIntegral_padicInt_iff_spectralNorm_le_one p E,
      NormedAlgebra.norm_eq_spectralNorm (Padic p)]
  rw [heq]
  exact isCompact_closedBall 0 1

end NormedIntegers

 

theorem integralClosure_padicInt_isDiscreteValuationRing
    (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] [Algebra (Padic p) E]
    [FiniteDimensional (Padic p) E] [Algebra (PadicInt p) E]
    [IsScalarTower (PadicInt p) (Padic p) E] :
    IsDiscreteValuationRing (integralClosure (PadicInt p) E) := by
  let : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField (Padic p) E
  let : NormedAlgebra (Padic p) E := spectralNorm.normedAlgebra (Padic p) E
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra (Padic p)
  let : Valued E ℝ≥0 := NormedField.toValued
  let : ProperSpace E := FiniteDimensional.proper (Padic p) E
  let : IsDiscreteValuationRing (Valued.integer E) := dvr_norm_integer E
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (integralClosureEquivInteger E p).symm

instance integralClosure_padicInt_dvr
    (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] [Algebra (Padic p) E]
    [FiniteDimensional (Padic p) E] [Algebra (PadicInt p) E]
    [IsScalarTower (PadicInt p) (Padic p) E] :
    IsDiscreteValuationRing (integralClosure (PadicInt p) E) :=
  integralClosure_padicInt_isDiscreteValuationRing p E

instance integralClosure_padicInt_finite_residue
    (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] [Algebra (Padic p) E]
    [FiniteDimensional (Padic p) E] [Algebra (PadicInt p) E]
    [IsScalarTower (PadicInt p) (Padic p) E] :
    Finite (IsLocalRing.ResidueField (integralClosure (PadicInt p) E)) := by
  let : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField (Padic p) E
  let : NormedAlgebra (Padic p) E := spectralNorm.normedAlgebra (Padic p) E
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra (Padic p)
  let : Valued E ℝ≥0 := NormedField.toValued
  let : ProperSpace E := FiniteDimensional.proper (Padic p) E
  let : Finite (IsLocalRing.ResidueField (Valued.integer E)) := finite_residue_norm_integer E
  exact Finite.of_equiv _ (IsLocalRing.ResidueField.mapEquiv
    (integralClosureEquivInteger E p).symm).toEquiv

open Polynomial
open scoped BigOperators

lemma isIntegral_pi_iff {R : Type*} [CommRing R] {I : Type*} [Finite I]
    {A : I → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] (x : ∀ i, A i) :
    IsIntegral R x ↔ ∀ i, IsIntegral R (x i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  constructor
  · intro hx i
    exact hx.map (Pi.evalAlgHom R A i)
  · intro h
    choose f hf hx using h
    refine ⟨∏ i, f i, monic_prod_of_monic _ _ (fun i _ => hf i), ?_⟩
    rw [← aeval_def]
    ext i
    rw [aeval_pi_apply₂,map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hx i)

 
def integralClosurePiEquiv {R : Type*} [CommRing R] {I : Type*} [Finite I]
    (A : I → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] :
    integralClosure R (∀ i, A i) ≃ₐ[R] ∀ i, integralClosure R (A i) where
  toFun x i := ⟨x.1 i,(isIntegral_pi_iff x.1).mp x.2 i⟩
  invFun y := ⟨fun i => (y i).1,(isIntegral_pi_iff _).mpr (fun i => (y i).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

 
def integralClosureEquiv {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) :
    integralClosure R A ≃ₐ[R] integralClosure R B where
  toFun x := ⟨e x.1,x.2.map e⟩
  invFun y := ⟨e.symm y.1,y.2.map e.symm⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul e x.1 y.1)
  map_add' x y := Subtype.ext (map_add e x.1 y.1)
  commutes' r := Subtype.ext (e.commutes r)


open IsDiscreteValuationRing IsLocalRing Module


lemma cardQuot_map_equiv {S R T : Type*} [CommRing S] [AddCommGroup R] [AddCommGroup T]
    [Module S R] [Module S T] (e : R ≃ₗ[S] T) (L : Submodule S R) :
    (L.map e.toLinearMap).cardQuot = L.cardQuot := by
  exact Nat.card_congr (Submodule.Quotient.equiv L (L.map e.toLinearMap) e rfl).symm.toEquiv


open MeasureTheory
open scoped ENNReal


def relativeElementIdeal {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  toPrincipalIdeal (𝓞 K) K a * I⁻¹

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_OrbitProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing


namespace PrimeDegreePackets

section Action
variable {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [MeasurableSpace X] [MulAction G X] [MeasurableSMul₂ G X]
    (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]

 

def orbitContainmentProbability (L : Set X) (x : X) : ℝ≥0∞ :=
  ∫⁻ g, L.indicator (fun _ => (1 : ℝ≥0∞)) (g • x) ∂ν

end Action
end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators
section
variable {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]



def localShellProbability
    [MeasurableSpace (∀ i, R i)ˣ]
    (ν : Measure (∀ i, R i)ˣ) (L : Set (∀ i, R i)) (k : ι → ℕ) : ℝ≥0∞ :=
  orbitContainmentProbability ν L (productDVRShell_nonempty R k).choose

end
end PrimeDegreePackets


open Filter
open scoped BigOperators Topology
namespace PrimeDegreePackets

def localMajorant (n p : ℕ) : ℝ :=
  ((1 - (p : ℝ)⁻¹) ^ n)⁻¹ * (1 + 4 * n / Real.sqrt p)

lemma localMajorant_nonneg (n p : ℕ) (hp : 1 ≤ p) : 0 ≤ localMajorant n p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hi : (p : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hp0).mpr hp1
  unfold localMajorant
  positivity

lemma localMajorant_tendsto_one (n : ℕ) :
    Tendsto (localMajorant n) atTop (𝓝 1) := by
  have hcast : Tendsto (fun p : ℕ => (p : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun p : ℕ => (p : ℝ)⁻¹) atTop (𝓝 0) := hcast.inv_tendsto_atTop
  have hs : Tendsto (fun p : ℕ => (Real.sqrt (p : ℝ))⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp hcast).inv_tendsto_atTop
  have ha := ((tendsto_const_nhds.sub hi).pow n).inv₀ (by simp : (1 - (0 : ℝ)) ^ n ≠ 0)
  have hb : Tendsto (fun p : ℕ => 1 + (4 * n) * (Real.sqrt (p : ℝ))⁻¹)
      atTop (𝓝 (1 + (4 * n) * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hs)
  change Tendsto (fun p : ℕ => ((1 - (p : ℝ)⁻¹) ^ n)⁻¹ *
    (1 + 4 * (n : ℝ) / Real.sqrt p)) atTop (𝓝 1)
  simpa [div_eq_mul_inv] using ha.mul hb



end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators


section
variable (n : ℕ) (S : Finset ℕ) [∀ p : S, Fact p.val.Prime]
    (ι : S → Type*) [∀ p, Fintype (ι p)]
    (R : ∀ p : S, ι p → Type*)
    [∀ p i, CommRing (R p i)] [∀ p i, IsDomain (R p i)]
    [∀ p i, IsDiscreteValuationRing (R p i)]
    [∀ p i, Algebra (PadicInt p.val) (R p i)]
    [∀ p i, TopologicalSpace (R p i)] [∀ p i, IsTopologicalRing (R p i)]
    [∀ p i, CompactSpace (R p i)] [∀ p i, T2Space (R p i)]
    [∀ p i, MeasurableSpace (R p i)] [∀ p i, BorelSpace (R p i)]
    [∀ p i, SecondCountableTopology (R p i)]
    [∀ p, MeasurableSpace (∀ i, R p i)ˣ] [∀ p, BorelSpace (∀ i, R p i)ˣ]
    (μ : ∀ p i, Measure (R p i)) [∀ p i, IsProbabilityMeasure (μ p i)]
    [∀ p i, (μ p i).IsAddHaarMeasure]
    (ν : ∀ p, Measure (∀ i, R p i)ˣ) [∀ p, IsProbabilityMeasure (ν p)]
    [∀ p, (ν p).IsMulRightInvariant]
    (L : ∀ p : S, Submodule (PadicInt p.val) (∀ i, R p i))
    [∀ p, Finite ((∀ i, R p i) ⧸ L p)]

def localIndexProduct : ℕ := ∏ p, (L p).cardQuot

def packetLocalWeight (k : ∀ p, ι p → ℕ) : ℝ≥0∞ :=
  ∏ p, localShellProbability (R p) (ν p) (L p) (k p)

def packetLocalNorm (k : ∀ p, ι p → ℕ) : ℝ≥0∞ :=
  ∏ p, shellNorm (R p) (k p)

end
end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory NumberField IsDiscreteValuationRing
open scoped ENNReal Pointwise nonZeroDivisors



lemma nonZeroDivisor_component_ne_zero {ι : Type*} {R : ι → Type*}
    [∀ i, CommRing (R i)] [∀ i, Nontrivial (R i)] {x : ∀ i, R i}
    (hx : x ∈ nonZeroDivisors (∀ i, R i)) (i : ι) : x i ≠ 0 := by
  classical
  intro hi
  have hzero : x * Pi.single i 1 = 0 := by
    funext j
    by_cases hij : j = i
    · subst j; simp [hi]
    · simp [Pi.single_eq_of_ne hij]
  have H := congrFun (hx.1 _ hzero) i
  simp at H

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology


namespace PrimeDegreePackets
open IsDiscreteValuationRing
open scoped BigOperators Pointwise NumberField nonZeroDivisors

lemma dvr_principal_eq_maximal_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (x : R) (hx : x ≠ 0) :
    Ideal.span ({x} : Set R) = IsLocalRing.maximalIdeal R ^ (addVal R x).toNat := by
  ext y
  rw [Ideal.mem_span_singleton, ← addVal_le_iff_dvd, mem_maximalIdeal_pow_iff_addVal,
    ENat.natCast_toNat (addVal_eq_top_iff.not.mpr hx)]

 

lemma product_dvr_principal_eq {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)]
    [∀ i, IsDiscreteValuationRing (R i)] (x : ∀ i, R i) (hx : ∀ i, x i ≠ 0) :
    Ideal.span ({x} : Set (∀ i, R i)) =
      Ideal.pi (fun i => IsLocalRing.maximalIdeal (R i) ^ (addVal (R i) (x i)).toNat) := by
  rw [← Ideal.pi_span]
  congr 1
  funext i
  exact dvr_principal_eq_maximal_pow _ (hx i)

lemma cardQuot_pi_restrictScalars {S : Type*} [CommRing S] {ι : Type*} [Fintype ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] [∀ i, Algebra S (R i)]
    (J : ∀ i, Ideal (R i)) :
    ((Ideal.pi J).restrictScalars S).cardQuot = ∏ i, (J i).cardQuot := by
  classical
  have h : (Ideal.pi J).restrictScalars S =
      Submodule.pi Set.univ (fun i => (J i).restrictScalars S) := by
    ext x
    simp only [Submodule.restrictScalars_mem, Ideal.mem_pi, Submodule.mem_pi,
      Set.mem_univ, forall_const]
  rw [h]
  rw [Submodule.cardQuot_apply]
  rw [Nat.card_congr (Submodule.quotientPi (fun i => (J i).restrictScalars S)).toEquiv,
    Nat.card_pi]
  rfl

lemma cardQuot_product_dvr_powers {S : Type*} [CommRing S] {ι : Type*} [Fintype ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)]
    [∀ i, IsDiscreteValuationRing (R i)] [∀ i, Algebra S (R i)] (k : ι → ℕ) :
    ((Ideal.pi (fun i => IsLocalRing.maximalIdeal (R i) ^ k i)).restrictScalars S).cardQuot =
      ∏ i, Nat.card (IsLocalRing.ResidueField (R i)) ^ k i := by
  rw [cardQuot_pi_restrictScalars]
  apply Finset.prod_congr rfl
  intro i _
  rw [cardQuot_pow_of_prime]
  · rfl
  · exact fun h => IsDiscreteValuationRing.not_isField (R i)
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)


lemma map_principal_restrictScalars {S R T : Type*} [CommRing S] [CommRing R] [CommRing T]
    [Algebra S R] [Algebra S T] (E : R ≃ₐ[S] T) (x : R) :
    ((Ideal.span ({x} : Set R)).restrictScalars S).map E.toLinearMap =
      (Ideal.span ({E x} : Set T)).restrictScalars S := by
  ext y
  rw [Submodule.mem_map_equiv]
  change E.symm y ∈ Ideal.span ({x} : Set R) ↔ y ∈ Ideal.span ({E x} : Set T)
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton, map_dvd_iff_dvd_symm]
  rfl


end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField
open scoped BigOperators Pointwise NumberField nonZeroDivisors ENNReal

 
def nonzeroIntegralIdealUnit {K : Type*} [Field K] [NumberField K]
    (J : {I : Ideal (𝓞 K) // I ≠ ⊥}) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (J.1 : FractionalIdeal (𝓞 K)⁰ K) (by simpa using J.2)

lemma nonzeroIntegralIdealUnit_le_one {K : Type*} [Field K] [NumberField K]
    (J : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
    (nonzeroIntegralIdealUnit J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 :=
  FractionalIdeal.coeIdeal_le_one

lemma integralIdeal_subgroup_map {K : Type*} [Field K] [NumberField K]
    (J : Ideal (𝓞 K)) :
    ((J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).toAddSubgroup =
      J.toAddSubgroup.map (algebraMap (𝓞 K) K).toAddMonoidHom := by
  ext x
  exact FractionalIdeal.mem_coeIdeal (𝓞 K)⁰

lemma absNorm_smul_integral {K : Type*} [Field K] [NumberField K]
    (J : Ideal (𝓞 K)) {x : K} (hx : x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    (Ideal.absNorm J : ℤ) • x ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨a,rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp hx
  have h : (Ideal.absNorm J : 𝓞 K) * a ∈ J := J.mul_mem_right a (Ideal.absNorm_mem J)
  have H := FractionalIdeal.mem_coeIdeal_of_mem (P := K) (𝓞 K)⁰ h
  simpa only [map_mul, map_natCast, zsmul_eq_mul, Int.cast_natCast] using H


def primaryIntegralIdeals (K : Type*) [Field K] [NumberField K] (S : Finset ℕ) :=
  {J : {I : Ideal (𝓞 K) // I ≠ ⊥} // ∀ p, p.Prime → p ∣ Ideal.absNorm J.1 → p ∈ S}

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
namespace PrimeDegreePackets

 
def IdealSupportedAt {K : Type*} [Field K] [NumberField K] (S : Finset ℕ)
    (I : Ideal (𝓞 K)) : Prop := ∀ p, p.Prime → p ∣ Ideal.absNorm I → p ∈ S

def IdealCoprimeTo {K : Type*} [Field K] [NumberField K] (S : Finset ℕ)
    (I : Ideal (𝓞 K)) : Prop := ∀ p ∈ S, ¬ p ∣ Ideal.absNorm I

lemma idealSupportedAt_one {K : Type*} [Field K] [NumberField K] (S : Finset ℕ) :
    IdealSupportedAt (K := K) S 1 := by
  intro p hp hd
  simp only [map_one] at hd
  exact (hp.not_dvd_one hd).elim

lemma idealCoprimeTo_one {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) : IdealCoprimeTo (K := K) S 1 := by
  intro p hp
  simpa only [map_one] using (hS p hp).not_dvd_one

lemma idealSupportedAt_mul {K : Type*} [Field K] [NumberField K]
    {S : Finset ℕ} {I J : Ideal (𝓞 K)} (hI : IdealSupportedAt S I)
    (hJ : IdealSupportedAt S J) : IdealSupportedAt S (I * J) := by
  intro p hp hd
  rw [map_mul] at hd
  rcases hp.dvd_mul.mp hd with hi | hj
  · exact hI p hp hi
  · exact hJ p hp hj

lemma idealCoprimeTo_mul {K : Type*} [Field K] [NumberField K]
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {I J : Ideal (𝓞 K)}
    (hI : IdealCoprimeTo S I) (hJ : IdealCoprimeTo S J) : IdealCoprimeTo S (I * J) := by
  intro p hp
  rw [map_mul]
  exact (hS p hp).not_dvd_mul (hI p hp) (hJ p hp)

lemma idealSupportedAt_of_norm_eq_prime_pow {K : Type*} [Field K] [NumberField K]
    {S : Finset ℕ} {I : Ideal (𝓞 K)} {p e : ℕ} (hp : p.Prime) (hmem : p ∈ S)
    (hI : Ideal.absNorm I = p ^ e) : IdealSupportedAt S I := by
  intro r hr hd
  rw [hI] at hd
  have hrp : r = p := (Nat.dvd_prime hp).mp (hr.dvd_of_dvd_pow hd) |>.resolve_left hr.ne_one
  exact hrp ▸ hmem

lemma idealCoprimeTo_of_norm_eq_prime_pow {K : Type*} [Field K] [NumberField K]
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {I : Ideal (𝓞 K)} {p e : ℕ}
    (hp : p.Prime) (hmem : p ∉ S) (hI : Ideal.absNorm I = p ^ e) : IdealCoprimeTo S I := by
  intro r hr hd
  rw [hI] at hd
  have hrp : r = p := (Nat.dvd_prime hp).mp ((hS r hr).dvd_of_dvd_pow hd)
    |>.resolve_left (hS r hr).ne_one
  exact hmem (hrp ▸ hr)

 

theorem exists_ideal_support_split {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (A : Ideal (𝓞 K)) : A ≠ ⊥ →
    ∃ I J : Ideal (𝓞 K), I ≠ ⊥ ∧ J ≠ ⊥ ∧ IdealSupportedAt S I ∧
      IdealCoprimeTo S J ∧ A = I * J := by
  classical
  induction A using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp
  | h₂ A hA =>
    intro _
    have ha : A = 1 := by simpa only [Ideal.isUnit_iff, Ideal.one_eq_top] using hA
    refine ⟨1,1,one_ne_zero,one_ne_zero,idealSupportedAt_one S,idealCoprimeTo_one S hS,?_⟩
    simpa using ha
  | h₃ A P hA hP ih =>
    intro _
    obtain ⟨I,J,hI,hJ,hsI,hcJ,hIJ⟩ := ih hA
    let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
    obtain ⟨p,e,_he,_hpP,hp,hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    by_cases hs : p ∈ S
    · refine ⟨P*I,J,mul_ne_zero hP.ne_zero hI,hJ,
        idealSupportedAt_mul (idealSupportedAt_of_norm_eq_prime_pow hp hs hnorm) hsI,hcJ,?_⟩
      rw [hIJ,mul_assoc]
    · refine ⟨I,P*J,hI,mul_ne_zero hP.ne_zero hJ,hsI,
        idealCoprimeTo_mul hS (idealCoprimeTo_of_norm_eq_prime_pow hS hp hs hnorm) hcJ,?_⟩
      rw [hIJ,mul_left_comm]

lemma ideal_support_norm_coprime {K : Type*} [Field K] [NumberField K]
    {S : Finset ℕ} {I J : Ideal (𝓞 K)} (hI : IdealSupportedAt S I)
    (hJ : IdealCoprimeTo S J) : (Ideal.absNorm I).Coprime (Ideal.absNorm J) :=
  Nat.coprime_of_dvd (fun p hp hi => hJ p (hI p hp hi))

lemma ideal_support_relprime {K : Type*} [Field K] [NumberField K]
    {S : Finset ℕ} {I J : Ideal (𝓞 K)} (hI : IdealSupportedAt S I)
    (hJ : IdealCoprimeTo S J) : IsRelPrime I J := by
  intro D hDI hDJ
  have hd : Ideal.absNorm D = 1 := Nat.eq_one_of_dvd_coprimes (ideal_support_norm_coprime hI hJ)
    (map_dvd Ideal.absNorm hDI) (map_dvd Ideal.absNorm hDJ)
  rw [Ideal.absNorm_eq_one_iff.mp hd]
  simpa only [Ideal.one_eq_top] using (isUnit_one : IsUnit (1 : Ideal (𝓞 K)))

lemma ideal_support_split_unique {K : Type*} [Field K] [NumberField K]
    {S : Finset ℕ} {I J I' J' : Ideal (𝓞 K)} (hI0 : I ≠ ⊥)
    (hI : IdealSupportedAt S I) (hJ : IdealCoprimeTo S J)
    (hI' : IdealSupportedAt S I') (hJ' : IdealCoprimeTo S J')
    (h : I * J = I' * J') : I = I' ∧ J = J' := by
  have hi : I ∣ I' := (ideal_support_relprime hI hJ').dvd_of_dvd_mul_right
    (h ▸ dvd_mul_right I J)
  have hi' : I' ∣ I := (ideal_support_relprime hI' hJ).dvd_of_dvd_mul_right
    (h.symm ▸ dvd_mul_right I' J')
  have he : I = I' := le_antisymm (Ideal.dvd_iff_le.mp hi') (Ideal.dvd_iff_le.mp hi)
  refine ⟨he,?_⟩
  rw [← he] at h
  exact mul_left_cancel₀ hI0 h

end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField
open scoped BigOperators Pointwise NumberField nonZeroDivisors ENNReal

 
def coprimeIntegralIdeals (K : Type*) [Field K] [NumberField K] (S : Finset ℕ) :=
  {J : {I : Ideal (𝓞 K) // I ≠ ⊥} // IdealCoprimeTo S J.1}

def idealSupportMul {K : Type*} [Field K] [NumberField K] (S : Finset ℕ)
    (A : primaryIntegralIdeals K S × coprimeIntegralIdeals K S) :
    {I : Ideal (𝓞 K) // I ≠ ⊥} :=
  ⟨A.1.1.1 * A.2.1.1, mul_ne_zero A.1.1.2 A.2.1.2⟩

lemma idealSupportMul_bijective {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) : Function.Bijective (idealSupportMul (K := K) S) := by
  constructor
  · rintro ⟨I,J⟩ ⟨I',J'⟩ h
    have hh := ideal_support_split_unique I.1.2 I.2 J.2 I'.2 J'.2 (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext (Subtype.ext hh.1)) (Subtype.ext (Subtype.ext hh.2))
  · intro A
    obtain ⟨I,J,hi,hj,hs,hc,he⟩ := exists_ideal_support_split S hS A.1 A.2
    exact ⟨⟨⟨⟨I,hi⟩,hs⟩,⟨⟨J,hj⟩,hc⟩⟩,Subtype.ext he.symm⟩

def idealSupportEquiv {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    primaryIntegralIdeals K S × coprimeIntegralIdeals K S ≃ {I : Ideal (𝓞 K) // I ≠ ⊥} :=
  Equiv.ofBijective (idealSupportMul S) (idealSupportMul_bijective S hS)

end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField IsDiscreteValuationRing
open scoped BigOperators Pointwise NumberField nonZeroDivisors ENNReal


lemma ideal_pi_injective {ι : Type*} [DecidableEq ι] (R : ι → Type*) [∀ i, CommRing (R i)] :
    Function.Injective (Ideal.pi (R := R)) := by
  intro I J h
  funext i
  ext x
  constructor
  · intro hx
    have H := h ▸ Ideal.single_mem_pi (I := I) hx
    simpa only [Pi.single_eq_same] using H i
  · intro hx
    have H := h.symm ▸ Ideal.single_mem_pi (I := J) hx
    simpa only [Pi.single_eq_same] using H i

lemma dvr_power_injective (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Function.Injective (fun k : ℕ => IsLocalRing.maximalIdeal R ^ k) := by
  intro k l h
  exact (pow_inj_of_not_isUnit
    (by simpa only [Ideal.isUnit_iff] using (IsLocalRing.maximalIdeal.isMaximal R).ne_top)
    (fun hz => IsDiscreteValuationRing.not_isField R (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hz))).mp h


end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_DivisorBounds
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
namespace PrimeDegreePackets



def nFoldDivisor (k m : ℕ) : ℕ := (ArithmeticFunction.zeta ^ k) m

end PrimeDegreePackets


namespace PrimeDegreePackets
open Finset Nat

 
def IsPowerful (m : ℕ) : Prop := m ≠ 0 ∧ ∀ p ∈ m.primeFactors, 2 ≤ m.factorization p



def powerfulCorrection (k m : ℕ) : ℝ := by
  classical
  exact if IsPowerful m then (nFoldDivisor (k + 1) m : ℝ) else 0

lemma powerfulCorrection_zero (k : ℕ) : powerfulCorrection k 0 = 0 := by
  simp [powerfulCorrection, IsPowerful]

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PowerfulIdeals
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset

open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
namespace PrimeDegreePackets.Sieve


def multipleMobius (P : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ k ∈ P.divisors, if d ∣ k then (μ (k / d) : ℝ) * y k else 0


def sieveDenominator (s : BoundingSieve) (z : ℕ) : ℝ :=
  ∑ k ∈ s.prodPrimes.divisors, if k ≤ z then s.selbergTerms k else 0

def optimalY (s : BoundingSieve) (z : ℕ) (k : ℕ) : ℝ :=
  if k ≤ z then (μ k : ℝ) * s.selbergTerms k / sieveDenominator s z else 0

def optimalWeight (s : BoundingSieve) (z : ℕ) (d : ℕ) : ℝ :=
  (s.nu d)⁻¹ * multipleMobius s.prodPrimes (optimalY s z) d

end PrimeDegreePackets.Sieve

open scoped BigOperators Classical
open Finset Nat
namespace PrimeDegreePackets.Sieve

def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

end PrimeDegreePackets.Sieve
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntervalSieve
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
namespace PrimeDegreePackets.Sieve
open Finset Nat ArithmeticFunction BoundingSieve

 
def reciprocalDensity : ArithmeticFunction ℝ := ⟨fun d => (d : ℝ)⁻¹, by simp⟩

lemma reciprocalDensity_multiplicative : reciprocalDensity.IsMultiplicative := by
  constructor
  · simp [reciprocalDensity]
  · intro a b _
    simp [reciprocalDensity, Nat.cast_mul, mul_comm]

 
def intervalSieve (a b P : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := Finset.Ioc a b
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := (b : ℝ) - a
  nu := reciprocalDensity
  nu_mult := reciprocalDensity_multiplicative
  nu_pos_of_prime := by
    intro p hp _
    exact inv_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

 
def truncatedTotientSum (P z : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, if d ≤ z then (d.totient : ℝ)⁻¹ else 0

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat



def mixtureMass (S T : Finset ℕ) (g : ℕ → ℝ) : ℝ :=
  (∏ p ∈ T, (1 - g p)) * ∏ p ∈ S \ T, g p

def softWeight (S : Finset ℕ) (g : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∏ p ∈ S, ((1 - g p) * (if p.Coprime m then 1 else 0) + g p)

end PrimeDegreePackets.Sieve

open scoped BigOperators
namespace PrimeDegreePackets.Sieve

 
def primePenalty (g : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => if m = 0 then 0 else ∏ p ∈ m.primeFactors, g p, by simp⟩



def logWeight (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => Real.log m * f m, by simp⟩

@[simp] lemma logWeight_apply (f : ArithmeticFunction ℝ) (m : ℕ) :
    logWeight f m = Real.log m * f m := rfl

lemma logWeight_mul (f g : ArithmeticFunction ℝ) :
    logWeight (f * g) = f * logWeight g + g * logWeight f := by
  rw [mul_comm g (logWeight f)]
  ext m
  rw [ArithmeticFunction.add_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply, logWeight_apply, ArithmeticFunction.mul_apply,
    Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  rintro ⟨d, e⟩ hde
  obtain ⟨hde, hm⟩ := Nat.mem_divisorsAntidiagonal.mp hde
  have hd : d ≠ 0 := by intro hd; simp_all
  have he : e ≠ 0 := by intro he; simp_all
  rw [← hde, Nat.cast_mul, Real.log_mul (by exact_mod_cast hd) (by exact_mod_cast he)]
  simp only [logWeight_apply]
  ring

 
def coefficientLogDerivation : Derivation ℝ (ArithmeticFunction ℝ) (ArithmeticFunction ℝ) where
  toFun := logWeight
  map_add' f g := by ext m; simp [mul_add]
  map_smul' r f := by ext m; simp [mul_left_comm]
  map_one_eq_zero' := by
    ext m
    by_cases hm : m = 1 <;> simp [hm]
  leibniz' f g := by
    change logWeight (f * g) = f * logWeight g + g * logWeight f
    exact logWeight_mul f g


def reciprocalCoefficients (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => f m / m, by simp⟩

@[simp] lemma reciprocalCoefficients_apply (f : ArithmeticFunction ℝ) (m : ℕ) :
    reciprocalCoefficients f m = f m / m := rfl

open scoped ArithmeticFunction.zeta

 
def divisorReciprocal (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  reciprocalCoefficients f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)


def largeFactorConvolution (f : ArithmeticFunction ℝ) (k H m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors.filter (H < ·), f d * (f ^ k) (m / d)

end PrimeDegreePackets.Sieve
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PenaltyEuler
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
namespace PrimeDegreePackets.Sieve
open Finset Nat

def smallPrimes (N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime

def penaltyEuler (g : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∏ p ∈ smallPrimes N, (1 + g p / ((p : ℝ) - 1))

end PrimeDegreePackets.Sieve


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_SieveConvolution
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
namespace PrimeDegreePackets.Sieve
open Finset Nat



def coefficientPenalty (k : ℕ) (b : ArithmeticFunction ℝ) (p : ℕ) : ℝ :=
  if p.Prime then b p / (k+1) else 0

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

def intervalConstant (k : ℕ) : ℝ :=
  (((12*(k+1)+2:ℕ):ℝ) * (2*((k+1:ℕ):ℝ)+1) * Real.exp (k+1))

def primeExponential (g : ℕ → ℝ) (k b : ℕ) : ℝ :=
  Real.exp (∑ p ∈ smallPrimes b, ((k+1:ℕ):ℝ) * g p / p)

end PrimeDegreePackets.Sieve

open Filter Topology
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealCoefficients
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology

open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
namespace PrimeDegreePackets

variable (K : Type*) [Field K] [NumberField K]

 

def idealCoefficient : ArithmeticFunction ℕ where
  toFun m := if m = 0 then 0 else Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = m}
  map_zero' := by simp

lemma ideal_eq_of_dvd_of_norm_eq {I J : Ideal (𝓞 K)} (hIJ : I ∣ J)
    (hI : Ideal.absNorm I ≠ 0) (hn : Ideal.absNorm I = Ideal.absNorm J) : I = J := by
  obtain ⟨A,rfl⟩ := hIJ
  have hA : Ideal.absNorm A = 1 := by
    rw [map_mul] at hn
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hI) (by simpa using hn.symm)
  rw [Ideal.absNorm_eq_one_iff.mp hA]
  simp

lemma ideals_relprime_of_norm_coprime {I J : Ideal (𝓞 K)}
    (h : (Ideal.absNorm I).Coprime (Ideal.absNorm J)) : IsRelPrime I J := by
  intro D hDI hDJ
  have hnorm : Ideal.absNorm D = 1 :=
    Nat.eq_one_of_dvd_coprimes h (map_dvd Ideal.absNorm hDI) (map_dvd Ideal.absNorm hDJ)
  rw [Ideal.absNorm_eq_one_iff.mp hnorm]
  simpa only [Ideal.one_eq_top] using (isUnit_one : IsUnit (1 : Ideal (𝓞 K)))

lemma ideal_multiplication_injective {m n : ℕ} (hm : m ≠ 0)
    (hmn : m.Coprime n) :
    Function.Injective (fun IJ : {I : Ideal (𝓞 K) // Ideal.absNorm I = m} ×
      {J : Ideal (𝓞 K) // Ideal.absNorm J = n} => (IJ.1.1 * IJ.2.1 : Ideal (𝓞 K))) := by
  intro IJ PQ heq
  dsimp only at heq
  have hIP : IJ.1.1 ∣ PQ.1.1 := by
    apply (ideals_relprime_of_norm_coprime K (I := IJ.1.1) (J := PQ.2.1) (by simpa [IJ.1.2,PQ.2.2] using hmn)).dvd_of_dvd_mul_right
    rw [← heq]
    exact dvd_mul_right _ _
  have hI : IJ.1.1 = PQ.1.1 := ideal_eq_of_dvd_of_norm_eq K hIP
    (by simpa [IJ.1.2] using hm) (by rw [IJ.1.2,PQ.1.2])
  have hJ : IJ.2.1 = PQ.2.1 := by
    have hi0 : IJ.1.1 ≠ 0 := by
      intro h
      have H := IJ.1.2
      rw [h,_root_.map_zero] at H
      exact hm H.symm
    rw [← hI] at heq
    exact mul_left_cancel₀ hi0 heq
  exact Prod.ext (Subtype.ext hI) (Subtype.ext hJ)

lemma prime_pow_dvd_coprime_product {p e m n : ℕ} (hp : p.Prime)
    (hmn : m.Coprime n) (hdiv : p^e ∣ m*n) : p^e ∣ m ∨ p^e ∣ n := by
  by_cases hpm : p ∣ m
  · exact Or.inl ((hmn.of_dvd_left hpm).pow_left e |>.dvd_of_dvd_mul_right hdiv)
  · exact Or.inr ((hp.coprime_iff_not_dvd.mpr hpm).pow_left e |>.dvd_of_dvd_mul_left hdiv)

 
lemma ideal_split_norm (I : Ideal (𝓞 K)) :
    ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → m.Coprime n → Ideal.absNorm I = m*n →
      ∃ J L : Ideal (𝓞 K), Ideal.absNorm J = m ∧ Ideal.absNorm L = n ∧ I = J*L := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    intro m n hm hn hmn heq
    have H : m*n = 0 := by simpa using heq.symm
    exact (mul_ne_zero hm hn H).elim
  | h₂ I hI =>
    intro m n hm hn hmn heq
    have htop : I = ⊤ := by simpa using hI
    have H : m*n = 1 := by simpa [htop] using heq.symm
    have hm1 : m = 1 := Nat.dvd_one.mp (H ▸ dvd_mul_right m n)
    have hn1 : n = 1 := Nat.dvd_one.mp (H ▸ dvd_mul_left n m)
    subst m; subst n
    refine ⟨⊤,⊤,by simp,by simp,?_⟩
    simpa using htop
  | h₃ I P hI hP IH =>
    have hPmax : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
    let := hPmax
    obtain ⟨p,e,he,hpP,hp,hPnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    have hP0 : Ideal.absNorm P ≠ 0 := by rw [hPnorm]; exact pow_ne_zero _ hp.ne_zero
    have hleft : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → m.Coprime n →
        Ideal.absNorm (P*I) = m*n → Ideal.absNorm P ∣ m →
        ∃ J L : Ideal (𝓞 K), Ideal.absNorm J = m ∧ Ideal.absNorm L = n ∧ P*I = J*L := by
      intro m n hm hn hmn heq hdiv
      obtain ⟨u,rfl⟩ := hdiv
      have hu : u ≠ 0 := by intro h; apply hm; simp [h]
      have hcop : u.Coprime n := hmn.of_dvd_left (dvd_mul_left _ _)
      have hnorm : Ideal.absNorm I = u*n := by
        rw [map_mul, mul_assoc] at heq
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hP0) heq
      obtain ⟨J,L,hJ,hL,hJL⟩ := IH u n hu hn hcop hnorm
      refine ⟨P*J,L,by simp [map_mul,hJ],hL,?_⟩
      rw [hJL,mul_assoc]
    intro m n hm hn hmn heq
    have hdiv : p^e ∣ m*n := by
      rw [← heq,map_mul,← hPnorm]
      exact dvd_mul_right _ _
    rcases prime_pow_dvd_coprime_product hp hmn hdiv with hpm | hpn
    · exact hleft m n hm hn hmn heq (by simpa [hPnorm] using hpm)
    · obtain ⟨L,J,hL,hJ,hJL⟩ := hleft n m hn hm hmn.symm
        (by simpa [mul_comm] using heq) (by simpa [hPnorm] using hpn)
      exact ⟨J,L,hJ,hL,by simpa [mul_comm] using hJL⟩

 
def idealNormProductEquiv (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n) :
    ({I : Ideal (𝓞 K) // Ideal.absNorm I = m} × {J : Ideal (𝓞 K) // Ideal.absNorm J = n}) ≃
      {I : Ideal (𝓞 K) // Ideal.absNorm I = m*n} := by
  let f : ({I : Ideal (𝓞 K) // Ideal.absNorm I = m} × {J : Ideal (𝓞 K) // Ideal.absNorm J = n}) →
      {I : Ideal (𝓞 K) // Ideal.absNorm I = m*n} := fun IJ =>
    ⟨IJ.1.1 * IJ.2.1, by simp [map_mul,IJ.1.2,IJ.2.2]⟩
  apply Equiv.ofBijective f
  constructor
  · intro IJ PQ heq
    exact ideal_multiplication_injective K hm hmn (congrArg Subtype.val heq)
  · intro I
    obtain ⟨J,L,hJ,hL,hI⟩ := ideal_split_norm K I m n hm hn hmn I.2
    exact ⟨(⟨J,hJ⟩,⟨L,hL⟩),Subtype.ext hI.symm⟩


lemma ideal_factor_prime_power {I P : Ideal (𝓞 K)} {p r : ℕ}
    (hp : p.Prime) (hI : Ideal.absNorm I = p^r) (hP : P ∈ normalizedFactors I) :
    (p : 𝓞 K) ∈ P ∧ p ≤ Ideal.absNorm P := by
  have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hmax : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  let := hmax
  obtain ⟨q,e,he,hqP,hq,hNorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
  have hdvd : P ∣ I := dvd_of_mem_normalizedFactors hP
  have h_qp : q ∣ p^r := by
    rw [← hI]
    exact dvd_trans (hNorm ▸ (dvd_pow_self q he.ne')) (map_dvd Ideal.absNorm hdvd)
  have heq : q = p := Nat.prime_eq_prime_of_dvd_pow hq hp h_qp
  subst q
  exact ⟨hqP, by rw [hNorm]; exact Nat.le_self_pow he.ne' p⟩


def idealsOverPrime (p : ℕ) : Finset (Ideal (𝓞 K)) :=
  (normalizedFactors (Ideal.span {(p : 𝓞 K)})).toFinset

lemma ideal_factor_mem_over {I P : Ideal (𝓞 K)} {p r : ℕ}
    (hp : p.Prime) (hI : Ideal.absNorm I = p^r) (hP : P ∈ normalizedFactors I) :
    P ∈ idealsOverPrime K p := by
  have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hspan : Ideal.span {(p : 𝓞 K)} ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] using hp.ne_zero
  rw [idealsOverPrime, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hspan]
  refine ⟨Ideal.isPrime_of_prime hprime, ?_⟩
  rw [Ideal.span_singleton_le_iff_mem]
  exact (ideal_factor_prime_power K hp hI hP).1

open Filter Topology Asymptotics
 
def idealCoefficientReal : ArithmeticFunction ℝ where
  toFun m := idealCoefficient K m
  map_zero' := by simp

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_MangoldtBounds
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid


namespace PrimeDegreePackets
variable (K : Type*) [Field K] [NumberField K]

 
def coprimeIdealCoefficient (q : ℕ) : ArithmeticFunction ℝ where
  toFun m := if m.Coprime q then idealCoefficientReal K m else 0
  map_zero' := by simp

end PrimeDegreePackets


namespace PrimeDegreePackets

 
def localEulerTailConstant (n : ℕ) : ℝ :=
  ∑' k : ℕ, ((n+1).multichoose (k+2) : ℝ) * (1/2:ℝ)^k

variable (K : Type*) [Field K] [NumberField K]

 

def idealPrimeEuler (p : ℕ) : ℝ :=
  ∑' k : ℕ, idealCoefficientReal K (p^k) / (p:ℝ)^k


def badPrimeEuler (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, idealPrimeEuler K p

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid


namespace PrimeDegreePackets

variable (K : Type*) [Field K] [NumberField K]

lemma idealsOverPrime_prime {p : ℕ} {P : Ideal (𝓞 K)}
    (hP : P ∈ idealsOverPrime K p) : Prime P :=
  UniqueFactorizationMonoid.prime_of_normalized_factor _ (Multiset.mem_toFinset.mp hP)

lemma idealsOverPrime_norm_power {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : P ∈ idealsOverPrime K p) : ∃ e : ℕ, Ideal.absNorm P = p^e := by
  have HD : Ideal.absNorm P ∣ Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) :=
    map_dvd Ideal.absNorm (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP))
  rw [Ideal.absNorm_span_natCast] at HD
  obtain ⟨e,-,he⟩ := (Nat.dvd_prime_pow hp).mp HD
  exact ⟨e,he⟩

 
def PrimaryIdeal (p : ℕ) :=
  {I : Ideal (𝓞 K) // I ≠ 0 ∧ ∀ P ∈ normalizedFactors I, P ∈ idealsOverPrime K p}

lemma primary_ideal_norm_power {p : ℕ} (hp : p.Prime) (I : PrimaryIdeal K p) :
    ∃ e : ℕ, Ideal.absNorm I.1 = p^e := by
  have HI := Ideal.prod_normalizedFactors_eq_self I.2.1
  rw [←HI, map_multiset_prod]
  have HA : ∀ m : Multiset (Ideal (𝓞 K)),
      (∀ P ∈ m, P ∈ idealsOverPrime K p) →
      ∃e : ℕ, (m.map Ideal.absNorm).prod = p^e := by
    intro m
    induction m using Multiset.induction_on with
    | empty => intro _; exact ⟨0,by simp⟩
    | @cons P m ih =>
      intro hm
      obtain ⟨e,he⟩ := idealsOverPrime_norm_power K hp (hm P (by simp))
      obtain ⟨f,hf⟩ := ih (fun Q hQ => hm Q (Multiset.mem_cons_of_mem hQ))
      exact ⟨e+f,by simp [he,hf,pow_add]⟩
  exact HA _ I.2.2

 

def primaryIdealMultisetEquiv (p : ℕ) :
    Multiset (idealsOverPrime K p) ≃ PrimaryIdeal K p := by
  classical
  let F (m : Multiset (idealsOverPrime K p)) := (m.map Subtype.val).prod
  have hfac (m : Multiset (idealsOverPrime K p)) :
      normalizedFactors (F m) = m.map Subtype.val := by
    apply normalizedFactors_prod_of_prime
    intro P hP
    obtain ⟨Q,-,rfl⟩ := Multiset.mem_map.mp hP
    exact idealsOverPrime_prime K Q.2
  have hF (m : Multiset (idealsOverPrime K p)) : F m ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hP
    obtain ⟨Q,-,hQ⟩ := Multiset.mem_map.mp hP
    exact (idealsOverPrime_prime K Q.2).ne_zero hQ
  let f (m : Multiset (idealsOverPrime K p)) : PrimaryIdeal K p :=
    ⟨F m,hF m,by
      intro P hP
      rw [hfac] at hP
      obtain ⟨Q,-,rfl⟩ := Multiset.mem_map.mp hP
      exact Q.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro m l h
    have H := congrArg (fun I : PrimaryIdeal K p => normalizedFactors I.1) h
    change normalizedFactors (F m) = normalizedFactors (F l) at H
    rw [hfac,hfac] at H
    exact Multiset.map_injective Subtype.val_injective H
  · intro I
    let m : Multiset (idealsOverPrime K p) :=
      (normalizedFactors I.1).attach.map (fun P => ⟨P.1,I.2.2 P.1 P.2⟩)
    refine ⟨m,Subtype.ext ?_⟩
    change ((normalizedFactors I.1).attach.map _ |>.map Subtype.val).prod = I.1
    simp only [Multiset.map_map,Function.comp_def,Multiset.attach_map_val]
    exact Ideal.prod_normalizedFactors_eq_self I.2.1

 

def primaryIdealNormEquiv (p : ℕ) (hp : p.Prime) :
    (Σe : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e}) ≃ PrimaryIdeal K p := by
  classical
  let f (a : Σe : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e}) : PrimaryIdeal K p :=
    ⟨a.2.1,by
      intro hz
      have H := a.2.2
      rw [hz,_root_.map_zero] at H
      exact (pow_ne_zero _ hp.ne_zero) H.symm,
      fun P hP => ideal_factor_mem_over K hp a.2.2 hP⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨e,I⟩ ⟨d,J⟩ he
    have hIJ : I.1 = J.1 := congrArg (fun I : PrimaryIdeal K p => I.1) he
    have hed : p^e = p^d := by rw [←I.2,←J.2,hIJ]
    have hed' := (Nat.pow_right_injective hp.two_le) hed
    subst d
    exact congrArg (Sigma.mk e) (Subtype.ext hIJ)
  · intro I
    obtain ⟨e,he⟩ := primary_ideal_norm_power K hp I
    exact ⟨⟨e,⟨I.1,he⟩⟩,Subtype.ext rfl⟩

end PrimeDegreePackets


namespace PrimeDegreePackets
open scoped ENNReal


variable (K : Type*) [Field K] [NumberField K]

@[simp] lemma primaryIdealMultisetEquiv_val (p : ℕ) (m : Multiset (idealsOverPrime K p)) :
    (primaryIdealMultisetEquiv K p m).val = (m.map Subtype.val).prod := rfl

@[simp] lemma primaryIdealNormEquiv_val (p : ℕ) (hp : p.Prime)
    (I : Σe : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e}) :
    (primaryIdealNormEquiv K p hp I).val = I.2.val := rfl

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid


namespace PrimeDegreePackets
open NumberField
open scoped BigOperators ENNReal nonZeroDivisors

lemma IdealCoprimeTo_primeFactors_iff {K : Type*} [Field K] [NumberField K]
    (q : ℕ) (hq : q ≠ 0) (I : Ideal (𝓞 K)) :
    IdealCoprimeTo q.primeFactors I ↔ (Ideal.absNorm I).Coprime q := by
  constructor
  · intro h
    apply Nat.coprime_of_dvd
    intro p hp hd hq'
    exact h p (Nat.mem_primeFactors.mpr ⟨hp,hq',hq⟩) hd
  · intro h p hp hd
    have := Nat.eq_one_of_dvd_coprimes h hd (Nat.mem_primeFactors.mp hp).2.1
    exact (Nat.prime_of_mem_primeFactors hp).ne_one this

 
def nonzeroIdealNormFiberEquiv {K : Type*} [Field K] [NumberField K]
    (m : ℕ) (hm : m ≠ 0) :
    {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // Ideal.absNorm I.1 = m} ≃
      {I : Ideal (𝓞 K) // Ideal.absNorm I = m} where
  toFun I := ⟨I.1.1,I.2⟩
  invFun I := ⟨⟨I.1,fun hz => hm (by simpa [hz] using I.2.symm)⟩,I.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def coprimeIdealSubtypeEquiv {K : Type*} [Field K] [NumberField K]
    (q : ℕ) (hq : q ≠ 0) :
    coprimeIntegralIdeals K q.primeFactors ≃
      {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // (Ideal.absNorm I.1).Coprime q} :=
  Equiv.subtypeEquivRight (fun I => IdealCoprimeTo_primeFactors_iff q hq I.1)



end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaResidues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
namespace PrimeDegreePackets

 

def realDedekindZeta (K : Type*) [Field K] [NumberField K] (s : ℝ) : ℝ :=
  (NumberField.dedekindZeta K (s : ℂ)).re



abbrev BoundedRealFields (N : ℕ) :=
  {K : {F : IntermediateField ℚ ℝ // FiniteDimensional ℚ F} //
    letI : NumberField K := @NumberField.mk _ _ inferInstance K.prop
    |NumberField.discr K| ≤ N}

instance boundedRealFields_numberField (N : ℕ) (K : BoundedRealFields N) :
    NumberField K.val := @NumberField.mk _ _ inferInstance K.val.prop

instance boundedRealFields_finite (N : ℕ) : Finite (BoundedRealFields N) :=
  (NumberField.finite_of_discr_bdd ℝ N).to_subtype



end PrimeDegreePackets


open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
namespace PrimeDegreePackets



lemma rowLattice_neg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    rowLattice (-A) = rowLattice A := by
  unfold rowLattice
  rw [show (Set.range fun i => (-A) i) = -(Set.range fun i => A i) by
    ext v
    simp [Set.mem_neg, funext_iff, neg_eq_iff_eq_neg]]
  exact Submodule.span_neg _

 

lemma normalizedMatrix_abs_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (hA : A.det ≠ 0) :
    |Matrix.det (|A.det| ^ (-(1 : ℝ) / n) • A)| = 1 := by
  have hpos : 0 < |A.det| := abs_pos.mpr hA
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Matrix.det_smul, Fintype.card_fin, abs_mul, abs_pow,
    abs_of_pos (Real.rpow_pos_of_pos hpos _), ← Real.rpow_natCast,
    ← Real.rpow_mul hpos.le]
  have he : (-(1 : ℝ) / n) * n = -1 := div_mul_cancel₀ _ hn0
  rw [he, Real.rpow_neg_one, inv_mul_cancel₀ hpos.ne']



open scoped NumberField nonZeroDivisors



lemma continuous_diagonalFlow (d : ℕ) : Continuous (@diagonalFlow d) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun u : LogCoordinates d =>
    Matrix.diagonal (Fin.snoc (fun i => Real.exp (u i)) (Real.exp (-∑ i, u i))) i j)
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [Fin.snoc_last]
      exact Real.continuous_exp.comp (continuous_finsetSum _ (fun i _ => continuous_apply i)).neg
    · simp only [Fin.snoc_castSucc]
      exact Real.continuous_exp.comp (continuous_apply k)
  · simp only [Matrix.diagonal_apply_ne _ hij]
    exact continuous_const

lemma continuous_orbitMap {d : ℕ} (x : X (d + 1)) : Continuous (orbitMap x) := by
  induction x using Quotient.inductionOn with
  | h g =>
    change Continuous (fun u => (Quotient.mk _ (g * diagonalFlow u) : X (d + 1)))
    exact continuous_quotient_mk'.comp (continuous_const.mul (continuous_diagonalFlow d))



lemma mem_diagonalOrbit_self {d : ℕ} (x : X (d + 1)) : x ∈ diagonalOrbit x :=
  ⟨0, orbitMap_zero x⟩

lemma diagonalOrbit_orbitMap {d : ℕ} (x : X (d + 1)) (u : LogCoordinates d) :
    diagonalOrbit (orbitMap x u) = diagonalOrbit x := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, rfl⟩
    exact ⟨u + v, orbitMap_add x u v⟩
  · rintro _ ⟨v, rfl⟩
    refine ⟨-u + v, ?_⟩
    rw [← orbitMap_add, ← add_assoc, add_neg_cancel, zero_add]

lemma one_mem_signMatrices (n : ℕ) : (1 : G n) ∈ signMatrices n := by
  constructor
  · intro i j hij
    exact Matrix.one_apply_ne hij
  · intro i
    exact Or.inl (Matrix.one_apply_eq i)

open scoped Pointwise

 

theorem finite_submodules_between {K : Type*} [Field K] [NumberField K]
    (J : Submodule ℤ K) (hJ : J.FG) (q : ℕ) (hq : q ≠ 0) :
    {N : Submodule ℤ K | (q : ℤ) • J ≤ N ∧ N ≤ J}.Finite := by
  let : Module.Finite ℤ J := Module.Finite.iff_fg.mpr hJ
  let A : Submodule ℤ J := (q : ℤ) • (⊤ : Submodule ℤ J)
  have ht : Module.IsTorsion ℤ (J ⧸ A) := by
    intro x
    refine ⟨⟨(q : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr (by exact_mod_cast hq)⟩, ?_⟩
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      change (q : ℤ) • x ∈ (q : ℤ) • (⊤ : Submodule ℤ J)
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x, Submodule.mem_top, rfl⟩
  let : Finite (J ⧸ A) := Module.finite_of_fg_torsion _ ht
  let : Finite (Set.Ici A) := Finite.of_equiv (Submodule ℤ (J ⧸ A)) A.comapMkQRelIso.toEquiv
  let f : {N : Submodule ℤ K | (q : ℤ) • J ≤ N ∧ N ≤ J} → Set.Ici A := fun N =>
    ⟨N.1.comap J.subtype, by
      intro x hx
      change x ∈ (q : ℤ) • (⊤ : Submodule ℤ J) at hx
      obtain ⟨y, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
      exact N.property.1 ((Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
        ⟨(y : K), y.property, rfl⟩)⟩
  apply Set.finite_coe_iff.mp
  apply Finite.of_injective f
  intro N P h
  apply Subtype.ext
  have hc : N.1.comap J.subtype = P.1.comap J.subtype := congrArg Subtype.val h
  have hm := congrArg (Submodule.map J.subtype) hc
  simpa only [Submodule.map_comap_subtype, inf_eq_right.mpr N.property.2,
    inf_eq_right.mpr P.property.2] using hm



open FractionalIdeal



theorem exists_diagonalFlow_of_positive {d : ℕ} (t : Fin (d + 1) → ℝ)
    (ht : ∀ i, 0 < t i) (hp : ∏ i, t i = 1) :
    ∃ u : LogCoordinates d, (diagonalFlow u).1 = Matrix.diagonal t := by
  let u : LogCoordinates d := fun i => Real.log (t i.castSucc)
  have hsum : ∑ i, Real.log (t i) = 0 := by
    rw [← Real.log_prod (fun i _ => (ht i).ne'), hp, Real.log_one]
  have hlast : Real.log (t (Fin.last d)) = -∑ i, u i := by
    rw [Fin.sum_univ_castSucc] at hsum
    dsimp only [u]
    linarith
  refine ⟨u, ?_⟩
  change Matrix.diagonal _ = Matrix.diagonal t
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, ← hlast, Real.exp_log (ht _)]
  · simp only [Fin.snoc_castSucc, u, Real.exp_log (ht _)]

 

theorem diagonal_eq_sign_mul_flow {d : ℕ} (g : G (d + 1))
    (hg : ∀ i j, i ≠ j → g.1 i j = 0) :
    ∃ w ∈ signMatrices (d + 1), ∃ u : LogCoordinates d, g = w * diagonalFlow u := by
  have hd : Matrix.diagonal (Matrix.diag g.1) = g.1 :=
    Matrix.IsDiag.diagonal_diag (fun i j hij => hg i j hij)
  let t := Matrix.diag g.1
  have hp : ∏ i, t i = 1 := by rw [← Matrix.det_diagonal, hd]; exact g.property
  have ht0 : ∀ i, t i ≠ 0 := fun i => by
    have H : ∏ i, t i ≠ 0 := by rw [hp]; exact one_ne_zero
    exact (Finset.prod_ne_zero_iff.mp H) i (Finset.mem_univ i)
  have ha : ∏ i, |t i| = 1 := by rw [← Finset.abs_prod, hp, abs_one]
  obtain ⟨u, hu⟩ := exists_diagonalFlow_of_positive (fun i => |t i|)
    (fun i => abs_pos.mpr (ht0 i)) ha
  let w : G (d + 1) := ⟨Matrix.diagonal (fun i => t i / |t i|), by
    rw [Matrix.det_diagonal, Finset.prod_div_distrib, hp, ha, _root_.div_one]⟩
  refine ⟨w, ⟨?_, ?_⟩, u, ?_⟩
  · intro i j hij
    exact Matrix.diagonal_apply_ne _ hij
  · intro i
    change Matrix.diagonal (fun i => t i / |t i|) i i = 1 ∨
      Matrix.diagonal (fun i => t i / |t i|) i i = -1
    simp only [Matrix.diagonal_apply_eq]
    rcases lt_or_gt_of_ne (ht0 i) with h | h
    · right
      rw [abs_of_neg h, div_neg, div_self (ht0 i)]
    · left
      rw [abs_of_pos h, div_self (ht0 i)]
  · apply Subtype.ext
    change g.1 = w.1 * (diagonalFlow u).1
    rw [hu, show w.1 = Matrix.diagonal (fun i => t i / |t i|) from rfl,
      Matrix.diagonal_mul_diagonal]
    rw [← hd]
    congr 1
    funext i
    exact (div_mul_cancel₀ (t i) (abs_ne_zero.mpr (ht0 i))).symm



lemma diagonal_inv {n : ℕ} (g : G n) (hg : ∀ i j, i ≠ j → g.1 i j = 0) :
    ∀ i j, i ≠ j → (g⁻¹).1 i j = 0 := by
  have hd : Matrix.diagonal (Matrix.diag g.1) = g.1 :=
    Matrix.IsDiag.diagonal_diag (fun i j hij => hg i j hij)
  intro i j hij
  rw [Matrix.SpecialLinearGroup.coe_inv, ← hd, Matrix.adjugate_diagonal,
    Matrix.diagonal_apply_ne _ hij]

lemma diagonal_mul {n : ℕ} (g h : G n)
    (hg : ∀ i j, i ≠ j → g.1 i j = 0) (hh : ∀ i j, i ≠ j → h.1 i j = 0) :
    ∀ i j, i ≠ j → (g * h).1 i j = 0 := by
  have hdg : Matrix.diagonal (Matrix.diag g.1) = g.1 :=
    Matrix.IsDiag.diagonal_diag (fun i j hij => hg i j hij)
  have hdh : Matrix.diagonal (Matrix.diag h.1) = h.1 :=
    Matrix.IsDiag.diagonal_diag (fun i j hij => hh i j hij)
  intro i j hij
  change (g.1 * h.1) i j = 0
  rw [← hdg, ← hdh, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_ne _ hij]



def normalizedLatticeQuotientMeasure {d : ℕ} (P : Submodule ℤ (Fin d → ℝ))
    (s : Set (Fin d → ℝ)) : Measure ((Fin d → ℝ) ⧸ P.toAddSubgroup) :=
  (volume s)⁻¹ • Measure.map QuotientAddGroup.mk (volume.restrict s)

instance matrixLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))

instance gLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace



def nonzeroSubmoduleMapEquiv {R V W : Type*} [Semiring R] [AddCommMonoid V]
    [Module R V] [AddCommMonoid W] [Module R W] (S : Submodule R V)
    (F : V →ₗ[R] W) (hF : Function.Injective F) :
    {v : S // (v : V) ≠ 0} ≃ {w : S.map F // (w : W) ≠ 0} :=
  (Submodule.equivMapOfInjective F hF S).toEquiv.subtypeEquiv (by
    intro v
    change (v : V) ≠ 0 ↔ F (v : V) ≠ 0
    constructor
    · intro hv h
      exact hv (hF (h.trans (map_zero F).symm))
    · rintro hv h
      exact hv (h ▸ map_zero F))



def nonzeroSubmoduleInclusionEquiv {R V : Type*} [Semiring R] [AddCommMonoid V]
    [Module R V] (N P : Submodule R V) (h : N ≤ P) :
    {a : N // (a : V) ≠ 0} ≃ {a : {a : P // (a : V) ≠ 0} // (a.1 : V) ∈ N} where
  toFun a := ⟨⟨⟨a.1,h a.1.property⟩,a.2⟩,a.1.property⟩
  invFun a := ⟨⟨a.1.1,a.2⟩,a.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl



def logFlowWeights {d : ℕ} (u : LogCoordinates d) : Fin (d+1) → ℝ :=
  Fin.snoc (fun i => Real.exp (u i)) (Real.exp (-∑ i, u i))

lemma relativeElementIdeal_le_one_iff {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ) :
    (relativeElementIdeal I a : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 ↔
      (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  constructor
  · intro h
    simp only [relativeElementIdeal,Units.val_mul,coe_toPrincipalIdeal] at h
    have H := mul_le_mul_right h (I : FractionalIdeal (𝓞 K)⁰ K)
    rw [mul_comm (I : FractionalIdeal (𝓞 K)⁰ K) (_ * _),mul_assoc,
      Units.inv_mul,mul_one,mul_one] at H
    exact H
  · intro h
    have H := mul_le_mul_right h (↑(I⁻¹) : FractionalIdeal (𝓞 K)⁰ K)
    simpa only [relativeElementIdeal,Units.val_mul,coe_toPrincipalIdeal,Units.mul_inv,Units.inv_mul,mul_comm,mul_left_comm,mul_assoc] using H

lemma relativeElementIdeal_class {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ) :
    ClassGroup.mk K (relativeElementIdeal I a) = (ClassGroup.mk K I)⁻¹ := by
  have hp : ClassGroup.mk K (toPrincipalIdeal (𝓞 K) K a) = 1 := by
    exact ClassGroup.mk_eq_one_iff.mpr (by
      rw [coe_toPrincipalIdeal,FractionalIdeal.coe_spanSingleton]
      exact ⟨⟨(a : K),rfl⟩⟩)
  simp only [relativeElementIdeal,map_mul,hp,map_inv,one_mul]

lemma relativeElementIdeal_eq_iff {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a b : Kˣ) :
    relativeElementIdeal I a = relativeElementIdeal I b ↔
      ∃ z : (𝓞 K)ˣ, z • (a : K) = (b : K) := by
  rw [relativeElementIdeal,relativeElementIdeal,mul_right_cancel_iff,Units.ext_iff,
    coe_toPrincipalIdeal,coe_toPrincipalIdeal,FractionalIdeal.spanSingleton_eq_spanSingleton]

 

def integralIdealClassFiber {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  {J : (FractionalIdeal (𝓞 K)⁰ K)ˣ //
    (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 ∧ ClassGroup.mk K J = (ClassGroup.mk K I)⁻¹}

 

def nonzeroIdealElements {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  {a : Kˣ // (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}

def relativeElementClassMap {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : nonzeroIdealElements I) : integralIdealClassFiber I :=
  ⟨relativeElementIdeal I a.val,(relativeElementIdeal_le_one_iff I a.val).mpr a.property,
    relativeElementIdeal_class I a.val⟩



def idealElementUnitAction {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (z : (𝓞 K)ˣ) (a : nonzeroIdealElements I) :
    nonzeroIdealElements I :=
  ⟨Units.map (algebraMap (𝓞 K) K).toMonoidHom z * a.val,
    show z • (a.val : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K) from
      (I : Submodule (𝓞 K) K).smul_mem (z : 𝓞 K) a.property⟩

lemma relativeElementClassMap_unitAction {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (z : (𝓞 K)ˣ) (a : nonzeroIdealElements I) :
    relativeElementClassMap I (idealElementUnitAction I z a) = relativeElementClassMap I a := by
  apply Subtype.ext
  apply ((relativeElementIdeal_eq_iff I a.val _).mpr ⟨z,rfl⟩).symm

lemma idealElementUnitAction_injective {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : nonzeroIdealElements I) :
    Function.Injective (fun z : (𝓞 K)ˣ => idealElementUnitAction I z a) := by
  intro z w h
  have he := congrArg (fun b : nonzeroIdealElements I => b.val) h
  change Units.map (algebraMap (𝓞 K) K).toMonoidHom z * a.val =
    Units.map (algebraMap (𝓞 K) K).toMonoidHom w * a.val at he
  have hh := congrArg (fun b : Kˣ => (b : K)) (mul_right_cancel he)
  apply Units.ext
  exact (IsFractionRing.injective (𝓞 K) K) hh

 

theorem exists_unique_unit_of_relativeElementClassMap_eq
    {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a b : nonzeroIdealElements I)
    (h : relativeElementClassMap I a = relativeElementClassMap I b) :
    ∃! z : (𝓞 K)ˣ, idealElementUnitAction I z a = b := by
  obtain ⟨z,hz⟩ := (relativeElementIdeal_eq_iff I a.val b.val).mp
    (congrArg Subtype.val h)
  refine ⟨z,?_,?_⟩
  · apply Subtype.ext
    apply Units.ext
    exact hz
  · intro w hw
    apply idealElementUnitAction_injective I a
    exact hw.trans (by apply Subtype.ext; apply Units.ext; exact hz.symm)



def nonzeroIdealElementEquiv {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    {a : (I : Submodule (𝓞 K) K).restrictScalars ℤ // (a : K) ≠ 0} ≃
      nonzeroIdealElements I where
  toFun a := ⟨Units.mk0 a.1.1 a.2,a.1.2⟩
  invFun a := ⟨⟨a.1,a.2⟩,a.1.ne_zero⟩
  left_inv _ := rfl
  right_inv a := by apply Subtype.ext; apply Units.ext; rfl



def integralFractionalIdeals (K : Type*) [Field K] [NumberField K] :=
  {J : (FractionalIdeal (𝓞 K)⁰ K)ˣ // (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1}



def coordinateBox {n : ℕ} (w : Fin n → ℝ) (ε : ℝ) : Set (Fin n → ℝ) :=
  {v | ∀ i, |v i-w i| ≤ ε}

def boxIndicator {n : ℕ} (w : Fin n → ℝ) (ε : ℝ) : (Fin n → ℝ) → ℝ≥0∞ :=
  (coordinateBox w ε).indicator (fun _ => 1)

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_StarkCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simple zeros in cyclic Artin factorizations

The cyclic step in Stark's exceptional-zero argument uses finite,
nonnegative orders of the Hecke factors. If their product has a simple
zero, exactly one factor has order one. Its zero-order character is
therefore a one-dimensional character, expressed using the actual
meromorphic orders in the cyclic factorization.
-/

open scoped BigOperators

namespace DukePrimeDegree

/-- Complex conjugation of a one-dimensional character. -/
def conjugateLinearCharacter {C : Type*} [Group C] (χ : C →* ℂˣ) : C →* ℂˣ :=
  (Units.map (starRingEnd ℂ).toMonoidHom).comp χ

@[simp] theorem conjugateLinearCharacter_apply {C : Type*} [Group C]
    (χ : C →* ℂˣ) (g : C) :
    (conjugateLinearCharacter χ g : ℂ) = starRingEnd ℂ (χ g : ℂ) := rfl

/-- A real-valued complex linear character regarded as a real character. -/
def realLinearCharacter {C : Type*} [Group C] (χ : C →* ℂˣ)
    (hr : ∀ g, (χ g : ℂ).im = 0) : C →* ℝˣ where
  toFun g :=
    { val := (χ g : ℂ).re
      inv := (χ g⁻¹ : ℂ).re
      val_inv := by
        have H := congrArg (fun z : ℂˣ => (z : ℂ).re) (χ.map_mul g g⁻¹)
        simp only [mul_inv_cancel, map_one, Units.val_mul, Units.val_one,
          Complex.mul_re, hr, mul_zero, sub_zero, Complex.one_re] at H
        exact H.symm
      inv_val := by
        have H := congrArg (fun z : ℂˣ => (z : ℂ).re) (χ.map_mul g⁻¹ g)
        simp only [inv_mul_cancel, map_one, Units.val_mul, Units.val_one,
          Complex.mul_re, hr, mul_zero, sub_zero, Complex.one_re] at H
        exact H.symm }
  map_one' := by apply Units.ext; simp
  map_mul' g h := by
    apply Units.ext
    change (χ (g * h) : ℂ).re = (χ g : ℂ).re * (χ h : ℂ).re
    rw [map_mul, Units.val_mul, Complex.mul_re, hr, hr]
    ring

@[simp] theorem realLinearCharacter_apply {C : Type*} [Group C]
    (χ : C →* ℂˣ) (hr : ∀ g, (χ g : ℂ).im = 0) (g : C) :
    (realLinearCharacter χ hr g : ℝ) = (χ g : ℂ).re := rfl

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CuspMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix


namespace PrimeDegreePackets

 

def logMomentConstant (d : ℕ) : ℝ :=
  ∑' j : ℕ, ((j : ℝ)+1)^d * Real.exp (-(j : ℝ))

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
namespace PrimeDegreePackets
open MeasureTheory Filter Set Topology
open scoped ENNReal NumberField BigOperators Classical

lemma finite_nonzeroIdeals_norm_le (K : Type*) [Field K] [NumberField K] (X : ℝ) :
    {I : {J : Ideal (𝓞 K) // J ≠ ⊥} | (Ideal.absNorm I.1:ℝ) ≤ X}.Finite := by
  have H := Set.Finite.preimage (f := fun I : {J : Ideal (𝓞 K) // J ≠ ⊥} => I.1)
    Subtype.val_injective.injOn (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌈X⌉₊)
  apply H.subset
  intro I hI
  exact_mod_cast hI.trans (Nat.le_ceil X)

 
def normBoundedIdeals (K : Type*) [Field K] [NumberField K] (X : ℝ) :
    Finset {J : Ideal (𝓞 K) // J ≠ ⊥} := (finite_nonzeroIdeals_norm_le K X).toFinset

@[simp] lemma mem_normBoundedIdeals (K : Type*) [Field K] [NumberField K]
    (X : ℝ) (I : {J : Ideal (𝓞 K) // J ≠ ⊥}) :
    I ∈ normBoundedIdeals K X ↔ (Ideal.absNorm I.1:ℝ) ≤ X :=
  Set.Finite.mem_toFinset _

end PrimeDegreePackets


open MeasureTheory Filter Set Module TopologicalSpace
namespace PrimeDegreePackets



def diagonalLogBox (d : ℕ) : Set (LogCoordinates d) :=
  {u | ∀ i, |u i| ≤ Real.log 2+1}

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_InverseEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal


namespace PrimeDegreePackets

 
def RelationDiameter {Y : Type*} (R : Y → Y → Prop) (E : Set Y) : Prop :=
  ∀ x ∈ E, ∀ y ∈ E, R x y

 

def StepCover {Y : Type*} (T : Y → Y) (R : Y → Y → Prop) (M : ℕ) : Prop :=
  ∀ E : Set Y, RelationDiameter R E → ∃ F : Fin M → Set Y,
    E ⊆ ⋃ i, F i ∧ ∀ i, F i ⊆ E ∧ RelationDiameter R (T '' F i)

end PrimeDegreePackets

open scoped BigOperators Topology ENNReal Classical
namespace PrimeDegreePackets

def visitCount {Y : Type*} (T : Y → Y) (B : Set Y) (N : ℕ) (x : Y) : ℕ :=
  ((Finset.range N).filter fun j => T^[j] x ∈ B).card

end PrimeDegreePackets

open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise

open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_AtomMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix


namespace PrimeDegreePackets

def entropyGoodSet {Y : Type*} (T : Y → Y) (K : Set Y) (ε : ℝ) (N : ℕ) : Set Y :=
  K ∩ (T^[(N-1)/2]) ⁻¹' K ∩ {x | (visitCount T Kᶜ N x : ℝ) ≤ ε*N}

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_EntropyMixtures
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix

open MeasureTheory ProbabilityTheory Filter Set
namespace PrimeDegreePackets

variable {Z Y ι : Type*} [MeasurableSpace Z] [MeasurableSpace Y]

 

def kernelCell (τ : Measure Z) (κ : Kernel Z Y) (Q : Z → ι) (i : ι) : Measure Y :=
  if τ {z | Q z = i} = 0 then κ ∘ₘ τ else κ ∘ₘ cond τ {z | Q z = i}

instance kernelCell_probability (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z Y) [IsMarkovKernel κ] (Q : Z → ι) (i : ι) :
    IsProbabilityMeasure (kernelCell τ κ Q i) := by
  unfold kernelCell
  split_ifs with h
  · infer_instance
  · have := cond_isProbabilityMeasure h
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_KernelEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set

open Set Filter
open scoped Topology

open scoped Classical
namespace PrimeDegreePackets

 
@[instance_reducible]
def actionInvariantSigma (H Y : Type*) [Group H] [MulAction H Y] [MeasurableSpace Y] :
    MeasurableSpace Y := ⨅ g : H, MeasurableSpace.invariants (fun y : Y => g • y)

lemma actionInvariantSigma_le (H Y : Type*) [Group H] [MulAction H Y]
    [mY : MeasurableSpace Y] : actionInvariantSigma H Y ≤ mY :=
  (iInf_le _ (1:H)).trans (MeasurableSpace.invariants_le _)

end PrimeDegreePackets

open scoped Topology ENNReal Classical
namespace PrimeDegreePackets

 
def orbitConvexHull {H Y : Type*} [Group H] [MulAction H Y] (f : Y → ℝ) : Set (Y → ℝ) :=
  convexHull ℝ (Set.range fun g : H => fun y : Y => f (g • y))

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_HaarUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology


namespace PrimeDegreePackets
open Filter Set Topology



def regularizedDedekindZeta (K : Type*) [Field K] [NumberField K] (h : ℝ) : ℝ :=
  h*(NumberField.dedekindZeta K (1+h)).re

def logRegularizedDedekindZeta (K : Type*) [Field K] [NumberField K] (h : ℝ) : ℝ :=
  Real.log (regularizedDedekindZeta K h)

end PrimeDegreePackets


namespace PrimeDegreePackets



def UniformZetaScaleBound (n : ℕ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ᶠ Q : ℝ in atTop,
    ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K],
      (K →+* ℝ) → Module.finrank ℚ K = n →
      |(NumberField.discr K : ℝ)| ≤ Q^2 →
      ∀ b : ℝ, Q^(3/4:ℝ) ≤ b →
        realDedekindZeta K (1+1/Real.log b) / Real.log b ≤
          A*NumberField.dedekindZeta_residue K

open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators


end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology


namespace PrimeDegreePackets



def archimedeanZetaTerm (n : ℕ) (s : ℝ) : ℝ :=
  (n : ℝ)/2 * ((Complex.digamma ((s:ℂ)/2)).re - Real.log Real.pi)

end PrimeDegreePackets


open MeasureTheory Filter Set Matrix
open scoped Topology Classical
namespace PrimeDegreePackets


def coordinateContractionWeights (d : ℕ) (j : Fin (d+1)) (i : Fin (d+1)) : ℝ :=
  (if i=j then ((d+1:ℕ):ℝ) else 0)-1

lemma coordinateContractionWeights_sum (d : ℕ) (j : Fin (d+1)) :
    ∑ i, coordinateContractionWeights d j i = 0 := by
  simp [coordinateContractionWeights,Finset.sum_sub_distrib]

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise


namespace PrimeDegreePackets

lemma vecMul_transvection_apply {n : ℕ} (v : Fin n → ℝ) (i j k : Fin n) (a : ℝ) :
    (v ᵥ* Matrix.transvection i j a) k = v k + if j=k then v i*a else 0 := by
  simp only [Matrix.transvection,Matrix.vecMul_add,Matrix.vecMul_one,Pi.add_apply]
  congr 1
  by_cases hjk : j=k
  · subst k
    simp [Matrix.vecMul,dotProduct,Matrix.single_apply,mul_ite]
  · simp [Matrix.vecMul,dotProduct,hjk]


end PrimeDegreePackets


open scoped Topology Classical ENNReal

open scoped Matrix Topology Classical
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory

open scoped ENNReal ProbabilityTheory
namespace PrimeDegreePackets

lemma compProd_map_measurableEquiv
    {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    (e : α ≃ᵐ γ) (f : β ≃ᵐ δ) :
    (μ ⊗ₘ κ).map (Prod.map e f) =
      μ.map e ⊗ₘ (κ.map f).comap e.symm e.symm.measurable := by
  ext S hS
  rw [Measure.map_apply (e.measurable.prodMap f.measurable) hS,
    Measure.compProd_apply ((e.measurable.prodMap f.measurable) hS),
    Measure.compProd_apply hS]
  rw [lintegral_map (Kernel.measurable_kernel_prodMk_left hS) e.measurable]
  apply lintegral_congr
  intro a
  rw [Kernel.comap_apply, e.symm_apply_apply,
    Kernel.map_apply' _ f.measurable _ (measurable_prodMk_left hS)]
  rfl

lemma fst_map_measurableEquiv
    {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (ρ : Measure (α × β)) (e : α ≃ᵐ γ) (f : β ≃ᵐ δ) :
    (ρ.map (Prod.map e f)).fst = ρ.fst.map e := by
  rw [Measure.fst, Measure.map_map measurable_fst (e.measurable.prodMap f.measurable),
    Measure.fst, Measure.map_map e.measurable measurable_fst]
  rfl

 

theorem condKernel_map_measurableEquiv
    {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace δ] [Nonempty δ]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (e : α ≃ᵐ γ) (f : β ≃ᵐ δ) :
    ∀ᵐ a ∂ρ.fst,
      (ρ.map (Prod.map e f)).condKernel (e a) = (ρ.condKernel a).map f := by
  let κ := (ρ.condKernel.map f).comap e.symm e.symm.measurable
  have hrec : ρ.map (Prod.map e f) = (ρ.map (Prod.map e f)).fst ⊗ₘ κ := by
    rw [fst_map_measurableEquiv, ← compProd_map_measurableEquiv,Measure.disintegrate]
  have H := eq_condKernel_of_measure_eq_compProd κ hrec
  rw [fst_map_measurableEquiv] at H
  have H' := ae_of_ae_map e.measurable.aemeasurable H
  filter_upwards [H'] with a ha
  simpa only [κ,Kernel.comap_apply,e.symm_apply_apply,Kernel.map_apply _ f.measurable] using ha.symm

end PrimeDegreePackets


namespace PrimeDegreePackets

def rootTimeScaling {n : ℕ} (ell : Fin n → ℝ) (i j : Fin n) (t : ℝ) : ℝ ≃ₜ ℝ :=
  Homeomorph.mulLeft₀ (Real.exp ((ell j-ell i)*t)) (Real.exp_ne_zero _)



end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_KernelScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace PrimeDegreePackets

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

 
def scaleBaseKernel (κ : Kernel α β) (w : α → ℝ≥0∞) (hw : Measurable w) : Kernel α β where
  toFun a := w a • κ a
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simpa only [Measure.smul_apply,smul_eq_mul,Pi.mul_apply] using hw.fun_mul (κ.measurable_coe hS)

lemma scaleBaseKernel_finite (κ : Kernel α β) [IsFiniteKernel κ]
    (w : α → ℝ≥0∞) (hw : Measurable w) (hw1 : ∀ a, w a ≤ 1) :
    IsFiniteKernel (scaleBaseKernel κ w hw) := by
  refine ⟨⟨κ.bound,κ.bound_lt_top,fun a => ?_⟩⟩
  change w a * κ a univ ≤ κ.bound
  calc
    _ ≤ 1 * κ a univ := mul_le_mul_of_nonneg_right (hw1 a) (bot_le)
    _ ≤ κ.bound := by simpa only [one_mul] using κ.measure_le_bound a univ

lemma compProd_scaleBaseKernel (μ : Measure α) [SFinite μ] (κ : Kernel α β)
    [IsSFiniteKernel κ] (w : α → ℝ≥0∞) (hw : Measurable w)
    [IsSFiniteKernel (scaleBaseKernel κ w hw)] :
    μ ⊗ₘ scaleBaseKernel κ w hw = μ.withDensity w ⊗ₘ κ := by
  ext S hS
  rw [Measure.compProd_apply hS,Measure.compProd_apply hS,
    lintegral_withDensity_eq_lintegral_mul μ hw (Kernel.measurable_kernel_prodMk_left hS)]
  rfl

lemma compProd_restrict_rectangle (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsSFiniteKernel κ]
    {U : Set α} {V : Set β} (hU : MeasurableSet U) (hV : MeasurableSet V) :
    (μ ⊗ₘ κ).restrict (U ×ˢ V) = μ.restrict U ⊗ₘ κ.restrict hV := by
  ext S hS
  rw [Measure.restrict_apply hS,Measure.compProd_apply (hS.inter (hU.prod hV)),
    Measure.compProd_apply hS,← lintegral_indicator hU]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ U
  · simp only [indicator_of_mem ha,Kernel.restrict_apply,
      Measure.restrict_apply (measurable_prodMk_left hS)]
    congr 1
    ext b
    simp [ha]
  · simp only [indicator_of_notMem ha]
    have he : Prod.mk a ⁻¹' (S ∩ U ×ˢ V) = ∅ := by ext b; simp [ha]
    rw [he,measure_empty]

lemma fst_compProd_withDensity (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsSFiniteKernel κ] :
    (μ ⊗ₘ κ).fst = μ.withDensity (fun a => κ a univ) := by
  ext U hU
  rw [Measure.fst_apply hU,withDensity_apply _ hU]
  rw [←Set.prod_univ]
  exact Measure.compProd_apply_prod hU MeasurableSet.univ

 

lemma restricted_conditional_marginal [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    {U : Set α} {V : Set β} (hU : MeasurableSet U) (hV : MeasurableSet V) :
    (ρ.restrict (U ×ˢ V)).fst =
      (ρ.fst.restrict U).withDensity (fun a => ρ.condKernel a V) := by
  have H := compProd_restrict_rectangle ρ.fst ρ.condKernel hU hV
  rw [Measure.disintegrate] at H
  rw [H,fst_compProd_withDensity]
  congr 1
  funext a
  simp only [Kernel.restrict_apply,Measure.restrict_apply MeasurableSet.univ,univ_inter]

 

theorem restricted_conditional_kernel [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    {U : Set α} {V : Set β} (hU : MeasurableSet U) (hV : MeasurableSet V) :
    ∀ᵐ a ∂ρ.fst.restrict U,
      ρ.condKernel a V • (ρ.restrict (U ×ˢ V)).condKernel a =
        (ρ.condKernel a).restrict V := by
  let σ := ρ.restrict (U ×ˢ V)
  let r : α → ℝ≥0∞ := fun a => ρ.condKernel a V
  have hr : Measurable r := ρ.condKernel.measurable_coe hV
  have hr1 : ∀ a, r a ≤ 1 := fun a => prob_le_one
  let κ := scaleBaseKernel σ.condKernel r hr
  have : IsFiniteKernel κ := scaleBaseKernel_finite σ.condKernel r hr hr1
  have he : ρ.fst.restrict U ⊗ₘ κ = ρ.fst.restrict U ⊗ₘ ρ.condKernel.restrict hV := by
    calc
      _ = (ρ.fst.restrict U).withDensity r ⊗ₘ σ.condKernel :=
        compProd_scaleBaseKernel _ _ r hr
      _ = σ.fst ⊗ₘ σ.condKernel := by
        rw [restricted_conditional_marginal ρ hU hV]
      _ = σ := Measure.disintegrate σ σ.condKernel
      _ = ρ.fst.restrict U ⊗ₘ ρ.condKernel.restrict hV := by
        rw [←compProd_restrict_rectangle _ _ hU hV,Measure.disintegrate]
  exact Kernel.ae_eq_of_compProd_eq he

end PrimeDegreePackets


open Set Filter Topology

open Set Filter Topology MeasureTheory

open MeasureTheory Set Filter Topology

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootOverlaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory

open MeasureTheory

open scoped BigOperators ENNReal

open NumberField Finset


namespace PrimeDegreePackets

 
def completionExponential (n : ℕ) (D : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s * (((Real.log D : ℝ) : ℂ) - n * (Real.log Real.pi : ℂ)) / 2)


end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_XiBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
namespace PrimeDegreePackets

def completedXiBoundaryValue (K : Type*) [Field K] [NumberField K] : ℂ :=
  completionExponential (Module.finrank ℚ K) |(NumberField.discr K:ℝ)| 1 *
    Complex.Gamma (1/2) ^ Module.finrank ℚ K * NumberField.dedekindZeta_residue K

end PrimeDegreePackets

open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

def torusProjection (x : d → ℝ) : UnitAddTorus d := fun i => x i

omit [Fintype d] in
lemma torusProjection_openQuotient : IsOpenQuotientMap (torusProjection (d := d)) := by
  exact IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

def torusRepresentative (y : UnitAddTorus d) : d → ℝ :=
  (UnitAddTorus.measurableEquivPiIoc (fun _ : d => 0) y).val

omit [Fintype d] in
lemma torusProjection_representative (y : UnitAddTorus d) :
    torusProjection (torusRepresentative y) = y := by
  exact (UnitAddTorus.measurableEquivPiIoc (fun _ : d => 0)).symm_apply_apply y

def unitCube : Set (d → ℝ) := {x | ∀ i, x i ∈ Ioc (0:ℝ) 1}

def fourierCharacter (m : d → ℤ) : C(d → ℝ,ℂ) :=
  (UnitAddTorus.mFourier (-m)).comp ⟨torusProjection,torusProjection_openQuotient.continuous⟩

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CoordinateLattices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

def coordinateLattice : Submodule ℤ (d → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ d))

instance coordinateLattice_discrete : DiscreteTopology (coordinateLattice (d := d)) :=
  ZSpan.discreteTopology_pi_basisFun

instance coordinateLattice_full : IsZLattice ℝ (coordinateLattice (d := d)) :=
  ⟨ZSpan.span_top (Pi.basisFun ℝ d)⟩

end PrimeDegreePackets.ThetaConstruction

open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def coordinateGaussian (A : (d → ℝ) ≃L[ℝ] E) (b : ℝ) : C(d → ℝ,ℂ) where
  toFun x := Complex.exp (-(b:ℂ) * ‖A x‖^2)
  continuous_toFun := by fun_prop

end PrimeDegreePackets.ThetaConstruction

open scoped FourierTransform

open scoped BigOperators SchwartzMap FourierTransform

open scoped BigOperators FourierTransform
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]



def coordinateBasis (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    (d → ℝ) ≃L[ℝ] EuclideanSpace ℝ d := (EuclideanSpace.equiv d ℝ).symm.trans B

end PrimeDegreePackets.ThetaConstruction

open MeasureTheory Set Filter Topology Module WithLp Asymptotics
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ThetaTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

def exponentialTail (a : ℝ) : ℝ → ℂ :=
  (Set.Ioi 1).indicator (fun t => (Real.exp (-a*t) : ℂ))

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_AnalyticLogarithms
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter

open Complex Set Metric Filter MeromorphicOn

open scoped Topology ComplexConjugate
namespace PrimeDegreePackets.AnalyticGrowth

def canonicalCorrection (R : ℝ) (ρ z : ℂ) : ℂ := conj ρ / ((R:ℂ)^2-conj ρ*z)

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth

 
def zeroMultiplicity (f : ℂ → ℂ) (z : ℂ) : ℤ := (meromorphicOrderAt f z).untop₀


def diskZeroCount (f : ℂ → ℂ) (R : ℝ) : ℝ :=
  ((∑ᶠ z, divisor f (closedBall (0:ℂ) R) z : ℤ) : ℝ)

end PrimeDegreePackets.AnalyticGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_MellinGrowth
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter


namespace PrimeDegreePackets.AnalyticGrowth

 
def HasSubquadraticGrowth (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ R : ℝ in atTop, ∀ z : ℂ,
    ‖z‖ ≤ R → ‖f z‖ ≤ Real.exp (ε * R^2)

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth

def zeroDiskFinset (f : ℂ → ℂ) (R : ℝ) : Finset ℂ :=
  ((divisor f (closedBall (0:ℂ) R)).finiteSupport (isCompact_closedBall 0 R)).toFinset

def diskPoleSum (f : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  ∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℂ) * (1/(z-ρ))

end PrimeDegreePackets.AnalyticGrowth


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZeroReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter


namespace PrimeDegreePackets.AnalyticGrowth

 
def realZeroPole (f : ℂ → ℂ) (σ : ℝ) (ρ : ℂ) : ℝ :=
  (zeroMultiplicity f ρ : ℝ)*(1/((σ:ℂ)-ρ)).re

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.HeckeMellin


def coordinates (d : ℕ) (u : Fin d → ℝ) (v : ℝ) : Fin (d+1) → ℝ :=
  Fin.snoc (fun i => u i + v/2) (-∑ i, u i + v/2)

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin

 
def logGammaKernel (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (s * (x : ℂ) - (Real.exp x : ℂ))


def gaussianLogKernel (s : ℂ) (r x : ℝ) : ℂ :=
  Complex.exp (s * (x : ℂ) - (r * Real.exp (2*x) : ℝ))

end PrimeDegreePackets.HeckeMellin


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RadialIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction



def realHeckeFactor (n : ℕ) (s : ℝ) : ℝ :=
  (2/(n : ℝ)) * ((1/2 : ℝ)*Real.pi^(-(s/2))*Real.Gamma (s/2))^n

end PrimeDegreePackets.HeckeMellin


open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealThetaXi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology

open Set

open Filter Set Module MeasureTheory
open scoped Topology NumberField

open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction


def traceDualIdeal {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ I.val) (FractionalIdeal.dual_ne_zero ℤ ℚ I.ne_zero)

end PrimeDegreePackets.HeckeMellin
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ThetaReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction


def traceDualClassEquiv (K : Type*) [Field K] [NumberField K] :
    ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
  (Equiv.inv _).trans (Equiv.mulLeft (ClassGroup.mk K (traceDualIdeal 1)))

end PrimeDegreePackets.HeckeMellin

open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_SubquadraticGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate

open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors

open Complex Set Filter Module

open Complex

open Complex Set Filter
namespace PrimeDegreePackets.AnalyticGrowth

 

def InNearOneBox (L : ℝ) (ρ : ℂ) : Prop :=
  1-1/(4*L) ≤ ρ.re ∧ |ρ.im| ≤ 1/(4*L)

end PrimeDegreePackets.AnalyticGrowth

open scoped Topology NumberField ComplexConjugate
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_FunctionalEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal

open IntermediateField Module
namespace PrimeDegreePackets


def embeddingPermutation {F K N : Type*} [Field F] [Field K] [Field N]
    [Algebra F K] [Algebra F N] (σ : N ≃ₐ[F] N) : Equiv.Perm (K →ₐ[F] N) where
  toFun f := σ.toAlgHom.comp f
  invFun f := σ.symm.toAlgHom.comp f
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp



end PrimeDegreePackets

open Module IntermediateField
open scoped BigOperators NumberField Pointwise


namespace PrimeDegreePackets

 

def smallIntegralBasisConstant (d : ℕ) : ℝ :=
  max 1 (2 / (1 / (2*(d+1)))^d + d / (2*(d+1)))

def closureDiscriminantConstant (d : ℕ) : ℝ :=
  (((d+1).factorial).factorial *
    (2*smallIntegralBasisConstant d)^((d+1)*(d+1).factorial))^2

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_NormalClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction


def idealClassDirichlet (K : Type*) [Field K] [NumberField K]
    (w : ClassGroup (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∑' J : integralFractionalIdeals K,
    w (ClassGroup.mk K J.1) * ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ)^(-s)

end PrimeDegreePackets.HeckeMellin


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter

open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
namespace PrimeDegreePackets.HeckeMellin

 
def conjugateClassCharacter {K : Type*} [Field K] [NumberField K]
    (χ : ClassGroup (𝓞 K) →* ℂ) : ClassGroup (𝓞 K) →* ℂ :=
  (starRingEnd ℂ).toMonoidHom.comp χ

@[simp] lemma conjugateClassCharacter_apply {K : Type*} [Field K] [NumberField K]
    (χ : ClassGroup (𝓞 K) →* ℂ) (c : ClassGroup (𝓞 K)) :
    conjugateClassCharacter χ c = conj (χ c) := rfl

@[simp] lemma conjugateClassCharacter_conjugate {K : Type*} [Field K] [NumberField K]
    (χ : ClassGroup (𝓞 K) →* ℂ) :
    conjugateClassCharacter (conjugateClassCharacter χ) = χ := by
  ext c
  simp

end PrimeDegreePackets.HeckeMellin

open Module
namespace PrimeDegreePackets

variable {G W : Type*} [Group G] [AddCommGroup W] [Module ℂ W]

 
def cosetFixedVector (H : Subgroup G) (ρ : Representation ℂ G W)
    (v : Representation.invariants (ρ.comp H.subtype)) : G ⧸ H → W :=
  Quotient.lift (fun g : G => ρ g v) (by
    intro a b hab
    have hv : ρ (a⁻¹*b) v = v := v.property ⟨a⁻¹*b,
      (QuotientGroup.leftRel_apply).mp hab⟩
    calc
      ρ a v = ρ a (ρ (a⁻¹*b) v) := congrArg (ρ a) hv.symm
      _ = ρ b v := by rw [← Module.End.mul_apply, ← map_mul]; simp)

@[simp] lemma cosetFixedVector_mk (H : Subgroup G) (ρ : Representation ℂ G W)
    (v : Representation.invariants (ρ.comp H.subtype)) (g : G) :
    cosetFixedVector H ρ v (QuotientGroup.mk g) = ρ g v := rfl

end PrimeDegreePackets


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]


def congruenceThetaFourierWeight {I : Type*} [Fintype I]
    (x : I → d → ℝ) (w : I → ℂ) (m : d → ℤ) : ℂ :=
  ∑ i, w i * UnitAddTorus.mFourier m (torusProjection (x i))

@[simp] lemma congruenceThetaFourierWeight_zero {I : Type*} [Fintype I]
    (x : I → d → ℝ) (w : I → ℂ) :
    congruenceThetaFourierWeight x w 0 = ∑ i, w i := by
  simp [congruenceThetaFourierWeight, UnitAddTorus.mFourier]



end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CongruenceLattices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]
local instance congruenceLatticesDecidableEq : DecidableEq d := Classical.decEq d

 
def integerCongruenceEquiv (N : ℕ) [NeZero N] :
    (d → ℤ) ≃ (d → Fin N) × (d → ℤ) where
  toFun z := (fun i => (Int.divModEquiv N (z i)).2,
    fun i => (Int.divModEquiv N (z i)).1)
  invFun rq i := (Int.divModEquiv N).symm (rq.2 i, rq.1 i)
  left_inv z := by
    funext i
    exact (Int.divModEquiv N).symm_apply_apply (z i)
  right_inv rq := by
    apply Prod.ext <;> funext i
    · exact congrArg Prod.snd ((Int.divModEquiv N).apply_symm_apply (rq.2 i, rq.1 i))
    · exact congrArg Prod.fst ((Int.divModEquiv N).apply_symm_apply (rq.2 i, rq.1 i))

 
def congruencePoint (N : ℕ) (r : d → Fin N) : d → ℝ :=
  fun i => (r i : ℝ) / N

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]
local instance congruenceLatticesGaussianDecidableEq : DecidableEq d := Classical.decEq d

end PrimeDegreePackets.ThetaConstruction


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PeriodicTheta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]
local instance periodicThetaDecidableEq : DecidableEq d := Classical.decEq d

def periodicPrimalWeight (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (z : d → ℤ) : ℂ :=
  w ((integerCongruenceEquiv N z).1)

def periodicDualWeight (N : ℕ) (w : (d → Fin N) → ℂ) : (d → ℤ) → ℂ :=
  congruenceThetaFourierWeight (congruencePoint N) w

end PrimeDegreePackets.ThetaConstruction


open MeasureTheory Module


namespace PrimeDegreePackets.ThetaConstruction
variable {d R : Type*} [Fintype d] [CommRing R]



local instance modulusScaledBasisDecidableEq_r142a9b_1 : DecidableEq d := Classical.decEq d
def modulusScaledBasis (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d :=
  ((LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ d) (N : ℝ)
    (Nat.cast_ne_zero.mpr (NeZero.ne N))).toContinuousLinearEquiv).trans B

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntegerEmbeddings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
open MeasureTheory Module
open scoped BigOperators Matrix NumberField nonZeroDivisors
namespace PrimeDegreePackets
open ThetaConstruction
variable {n : ℕ} {K : Type*} [Field K] [NumberField K]



def orderedIntegerBasis (hn : finrank ℚ K = n) : Basis (Fin n) ℤ (𝓞 K) :=
  (NumberField.RingOfIntegers.basis K).reindex (Fintype.equivFinOfCardEq (by
    rw [← finrank_eq_card_basis (NumberField.integralBasis K)]
    exact hn))



end PrimeDegreePackets

open scoped BigOperators NumberField nonZeroDivisors


namespace PrimeDegreePackets.ThetaConstruction
variable {d R : Type*} [Fintype d] [CommRing R]
local instance integerEmbeddingsDecidableEq : DecidableEq d := Classical.decEq d

def moduleResidueEquiv {M : Type*} [AddCommGroup M] (b : Basis d ℤ M)
    (N : ℕ) [NeZero N] : (d → Fin N) ≃ ModN M N :=
  (Equiv.piCongrRight fun _ : d => (ZMod.finEquiv N).toEquiv).trans
    (ModN.basis b).equivFun.symm.toEquiv

end PrimeDegreePackets.ThetaConstruction


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_GaussianMellin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
open MeasureTheory Module
open scoped BigOperators Matrix NumberField nonZeroDivisors
open scoped BigOperators NumberField nonZeroDivisors
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]
local instance averagedPeriodicThetaDecidableEq : DecidableEq d := Classical.decEq d

end PrimeDegreePackets.ThetaConstruction


open MeasureTheory Module WithLp Set
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrincipalUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
open MeasureTheory Module
open scoped BigOperators Matrix NumberField nonZeroDivisors
open scoped BigOperators NumberField nonZeroDivisors
open MeasureTheory Module WithLp Set
open scoped BigOperators NumberField ENNReal
open scoped BigOperators NumberField
open scoped BigOperators NumberField ENNReal nonZeroDivisors


namespace PrimeDegreePackets

 

theorem exists_simultaneous_ideal_generator {R : Type*} [CommRing R]
    [IsDedekindDomain R] (I : Ideal R) (hI : I ≠ ⊥)
    (s : Finset (Ideal R)) (hprime : ∀ P ∈ s, Prime P) :
    ∃ x ∈ I, ∀ P ∈ s, x ∉ P * I := by
  classical
  have hex : ∀ P : s, ∃ x ∈ I, x ∉ P.val * I := by
    intro P
    have hP : P.val ≠ 1 := (hprime P P.property).ne_one
    have hne : P.val * I ≠ I := by
      intro H
      apply hP
      exact mul_right_cancel₀ hI (H.trans (one_mul I).symm)
    have hnle : ¬ I ≤ P.val * I := fun H => hne (le_antisymm Ideal.mul_le_right H)
    exact Set.not_subset.mp hnle
  choose x hx hnx using hex
  have he : ∀ P : s, ∃ e : R, ∀ Q : s,
      e - (if Q = P then 1 else 0) ∈ Q.val := by
    intro P
    obtain ⟨e,he⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (fun Q : Ideal R => Q)
      (fun _ => 1) hprime (by intros; assumption)
      (fun Q : s => if Q = P then (1:R) else 0)
    exact ⟨e, fun Q => by simpa using he Q Q.property⟩
  choose e he using he
  refine ⟨∑ P : s, e P * x P, I.sum_mem (fun P _ => I.mul_mem_left _ (hx P)), ?_⟩
  intro Q hQ hmem
  let q : s := ⟨Q,hQ⟩
  have H : (∑ P : s, e P * x P) - x q ∈ Q * I := by
    have Hsum : (∑ P : s, (e P - if q = P then 1 else 0) * x P) ∈ Q * I :=
      (Q * I).sum_mem fun P _ => Ideal.mul_mem_mul (he P q) (hx P)
    convert Hsum using 1
    all_goals try with_reducible_and_instances rfl
    simp only [sub_mul, Finset.sum_sub_distrib]
    simp
  exact hnx q ((Q * I).sub_mem hmem H |> fun H' => by simpa using H')

lemma exists_nonzero_simultaneous_ideal_generator {R : Type*} [CommRing R]
    [IsDedekindDomain R] (I : Ideal R) (hI : I ≠ ⊥)
    (s : Finset (Ideal R)) (hprime : ∀ P ∈ s, Prime P) :
    ∃ x ∈ I, x ≠ 0 ∧ ∀ P ∈ s, x ∉ P * I := by
  classical
  obtain rfl | hs := s.eq_empty_or_nonempty
  · obtain ⟨x,hx,hx0⟩ := I.ne_bot_iff.mp hI
    exact ⟨x,hx,hx0, by simp⟩
  · obtain ⟨x,hx,H⟩ := exists_simultaneous_ideal_generator I hI s hprime
    refine ⟨x,hx,?_,H⟩
    obtain ⟨P,hP⟩ := hs
    rintro rfl
    exact H P hP (Ideal.zero_mem _)

 

theorem exists_coprime_ideal_product {R : Type*} [CommRing R]
    [IsDedekindDomain R] (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥) :
    ∃ (x : R) (J : Ideal R), x ≠ 0 ∧ x ∈ I ∧ J ≠ ⊥ ∧
      IsCoprime J M ∧ Ideal.span {x} = I * J := by
  classical
  obtain ⟨x,hx,hx0,Hx⟩ := exists_nonzero_simultaneous_ideal_generator I hI
    (UniqueFactorizationMonoid.factors M).toFinset
    (fun P hP => UniqueFactorizationMonoid.prime_of_factor P
      (Multiset.mem_toFinset.mp hP))
  obtain ⟨J,hJ⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hx)
  have hJ0 : J ≠ ⊥ := by
    intro H
    rw [H, Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ
    exact hx0 hJ
  refine ⟨x,J,hx0,hx,hJ0,?_,hJ⟩
  apply Ideal.coprime_of_no_prime_ge
  intro P hJP hMP hP
  have hP0 : P ≠ ⊥ := ne_bot_of_le_ne_bot hM hMP
  obtain ⟨Q,hQ,heq⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hM
    (Ideal.prime_of_isPrime hP0 hP).irreducible (Ideal.dvd_iff_le.mpr hMP)
  have HPQ : P = Q := associated_iff_eq.mp heq
  subst Q
  apply Hx P (Multiset.mem_toFinset.mpr hQ)
  have hle : Ideal.span {x} ≤ P * I := by
    rw [hJ, mul_comm I J]
    simpa only [mul_comm I J, mul_comm I P] using mul_le_mul_right hJP I
  exact hle (Ideal.subset_span (by simp))

open scoped nonZeroDivisors in
 

theorem exists_coprime_class_representative {R : Type*} [CommRing R]
    [IsDedekindDomain R] (M : Ideal R) (hM : M ≠ ⊥) (c : ClassGroup R) :
    ∃ J : (Ideal R)⁰, IsCoprime J.val M ∧ ClassGroup.mk0 J = c := by
  obtain ⟨I,hI⟩ := ClassGroup.mk0_surjective c⁻¹
  obtain ⟨x,J,hx0,hx,hJ0,hcop,hprod⟩ := exists_coprime_ideal_product I.val M
    (mem_nonZeroDivisors_iff_ne_zero.mp I.property) hM
  let Jn : (Ideal R)⁰ := ⟨J,mem_nonZeroDivisors_iff_ne_zero.mpr hJ0⟩
  refine ⟨Jn,hcop,?_⟩
  have H : ClassGroup.mk0 I * ClassGroup.mk0 Jn = 1 := by
    rw [← map_mul]
    apply (ClassGroup.mk0_eq_one_iff (I * Jn).property).mpr
    change (I.val * J).IsPrincipal
    rw [← hprod]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  rw [hI] at H
  have He := congrArg (fun z : ClassGroup R => c * z) H
  simpa only [← mul_assoc,mul_inv_cancel,one_mul,mul_one] using He

end PrimeDegreePackets


namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
variable {K : Type*} [Field K] [NumberField K]

def coprimeClassRepresentative (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (c : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  (exists_coprime_class_representative M hM c).choose

lemma coprimeClassRepresentative_spec (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (c : ClassGroup (𝓞 K)) :
    IsCoprime (coprimeClassRepresentative M hM c).val M ∧
      ClassGroup.mk0 (coprimeClassRepresentative M hM c) = c :=
  (exists_coprime_class_representative M hM c).choose_spec



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayCharacter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical ComplexConjugate
namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction

 

lemma quotient_isUnit_iff_span_coprime {R : Type*} [CommRing R]
    (M : Ideal R) (a : R) :
    IsUnit (Ideal.Quotient.mk M a) ↔ IsCoprime (Ideal.span {a}) M := by
  rw [Ideal.isCoprime_iff_sup_eq]
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have he : a * b - 1 ∈ M := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp only [map_sub, map_mul, map_one, hb, sub_self]
    apply (Ideal.eq_top_iff_one _).mpr
    have hmem : a * b ∈ Ideal.span {a} ⊔ M :=
      Submodule.mem_sup_left (Ideal.mem_span_singleton.mpr (dvd_mul_right a b))
    have hm : a * b - 1 ∈ Ideal.span {a} ⊔ M := Submodule.mem_sup_right he
    simpa only [sub_sub_cancel] using (Ideal.span {a} ⊔ M).sub_mem hmem hm
  · intro h
    have h1 : (1 : R) ∈ Ideal.span {a} ⊔ M := by rw [h]; trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hx
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk M b, ?_⟩
    have he := congrArg (Ideal.Quotient.mk M) hxy
    simpa only [map_add, map_mul, map_one,
      Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero] using he

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayUnramified
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical
namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ}


def badPrimes (N : ℕ) : Finset Nat.Primes := N.primeFactors.subtype Nat.Prime

end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ArtinEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module
open scoped NumberField Classical BigOperators
namespace PrimeDegreePackets.GaloisIdealCharacter

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [IsCyclic (E ≃ₐ[F] E)]
attribute [local instance] IsCyclic.commGroup
local instance artinCharacterFintype : Fintype ((E ≃ₐ[F] E) →* ℂˣ) := Fintype.ofFinite _
local instance artinPrimesOverFintype (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    Fintype (Ideal.primesOver P.asIdeal (𝓞 E)) := Fintype.ofFinite _



end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_FrobeniusCoset
attribute [-instance] _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module
open scoped NumberField Pointwise Classical
namespace PrimeDegreePackets.GaloisIdealCharacter

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

local instance fixingRingGroup (L : IntermediateField F E) :
    IsGaloisGroup L.fixingSubgroup (𝓞 L) (𝓞 E) :=
  IsGaloisGroup.of_mulEquiv (IntermediateField.fixingSubgroupEquiv L)
    (fun _ _ => rfl)

local instance fixingRingCommutes (L : IntermediateField F E) :
    SMulCommClass L.fixingSubgroup (𝓞 L) (𝓞 E) :=
  (fixingRingGroup F E L).commutes

omit [FiniteDimensional F E] in
lemma under_fixing_smul (L : IntermediateField F E) (Q : Ideal (𝓞 E))
    (h : L.fixingSubgroup) :
    ((h.val : E ≃ₐ[F] E) • Q).under (𝓞 L) = Q.under (𝓞 L) := by
  change (h • Q).under (𝓞 L) = _
  exact Ideal.under_smul (𝓞 L) Q h

def cosetPrime (L : IntermediateField F E) (Q : Ideal (𝓞 E)) :
    (E ≃ₐ[F] E) ⧸ L.fixingSubgroup → Ideal (𝓞 L) := by
  refine Quotient.lift (fun a : E ≃ₐ[F] E => (a⁻¹ • Q).under (𝓞 L)) ?_
  intro a b hab
  have hm : a⁻¹ * b ∈ L.fixingSubgroup := QuotientGroup.leftRel_apply.mp hab
  have he : b⁻¹ = (a⁻¹ * b)⁻¹ * a⁻¹ := by group
  rw [he, mul_smul]
  exact (under_fixing_smul F E L (a⁻¹ • Q) ⟨(a⁻¹ * b)⁻¹, L.fixingSubgroup.inv_mem hm⟩).symm

omit [FiniteDimensional F E] in
@[simp] lemma cosetPrime_mk (L : IntermediateField F E) (Q : Ideal (𝓞 E))
    (a : E ≃ₐ[F] E) :
    cosetPrime F E L Q (QuotientGroup.mk a) = (a⁻¹ • Q).under (𝓞 L) := rfl

omit [FiniteDimensional F E] in
lemma cosetPrime_stabilizer_smul (L : IntermediateField F E) (Q : Ideal (𝓞 E))
    (h : MulAction.stabilizer (E ≃ₐ[F] E) Q)
    (a : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup) :
    cosetPrime F E L Q (h • a) = cosetPrime F E L Q a := by
  induction a using Quotient.inductionOn
  rename_i a
  change ((h.val * a)⁻¹ • Q).under (𝓞 L) = _
  rw [mul_inv_rev, mul_smul]
  have : h.val⁻¹ • Q = Q := h⁻¹ |>.property
  rw [this]
  rfl

section GroupCosets
variable {G A : Type*} [Group G] [MulAction G A]

lemma mem_coset_stabilizer_iff (H : Subgroup G) (x : A) (a : G)
    (d : MulAction.stabilizer G x) :
    d ∈ MulAction.stabilizer (MulAction.stabilizer G x) (QuotientGroup.mk a : G ⧸ H) ↔
      a⁻¹ * d.val * a ∈ H := by
  rw [MulAction.mem_stabilizer_iff]
  change (QuotientGroup.mk (d.val * a) : G ⧸ H) = QuotientGroup.mk a ↔ _
  rw [eq_comm, QuotientGroup.eq]
  simp only [mul_assoc]

 

def cosetStabilizerEquiv (H : Subgroup G) (x : A) (a : G) :
    MulAction.stabilizer (MulAction.stabilizer G x) (QuotientGroup.mk a : G ⧸ H) ≃
      MulAction.stabilizer H (a⁻¹ • x) where
  toFun d := ⟨⟨a⁻¹ * d.val.val * a, (mem_coset_stabilizer_iff H x a d.val).mp d.property⟩,
    by
      change (a⁻¹ * d.val.val * a) • (a⁻¹ • x) = a⁻¹ • x
      rw [mul_smul, mul_smul, smul_inv_smul, d.val.property]⟩
  invFun h := ⟨⟨a * h.val.val * a⁻¹, by
      change (a * h.val.val * a⁻¹) • x = x
      rw [mul_smul, mul_smul]
      rw [show h.val.val • (a⁻¹ • x) = a⁻¹ • x from h.property, smul_inv_smul]⟩, by
    apply (mem_coset_stabilizer_iff H x a _).mpr
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h.val.property⟩
  left_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    change a * (a⁻¹ * d.val.val * a) * a⁻¹ = d.val.val
    group
  right_inv h := by
    apply Subtype.ext
    apply Subtype.ext
    change a⁻¹ * (a * h.val.val * a⁻¹) * a = h.val.val
    group
end GroupCosets

lemma cosetPrime_eq_iff (L : IntermediateField F E) (Q : Ideal (𝓞 E)) [Q.IsPrime]
    (a b : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup) :
    cosetPrime F E L Q a = cosetPrime F E L Q b ↔
      MulAction.orbitRel (MulAction.stabilizer (E ≃ₐ[F] E) Q) _ a b := by
  constructor
  · induction a using Quotient.inductionOn
    rename_i a
    induction b using Quotient.inductionOn
    rename_i b
    intro he
    change (a⁻¹ • Q).under (𝓞 L) = (b⁻¹ • Q).under (𝓞 L) at he
    let : (a⁻¹ • Q).IsPrime := Ideal.IsPrime.smul _
    let : (b⁻¹ • Q).IsPrime := Ideal.IsPrime.smul _
    obtain ⟨h, hh⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
      (𝓞 L) (𝓞 E) L.fixingSubgroup (b⁻¹ • Q) (a⁻¹ • Q) he.symm
    have hd : a * h.val * b⁻¹ ∈ MulAction.stabilizer (E ≃ₐ[F] E) Q := by
      change (a * h.val * b⁻¹) • Q = Q
      rw [mul_smul, mul_smul]
      rw [show h.val • (b⁻¹ • Q) = a⁻¹ • Q from hh.symm, smul_inv_smul]
    refine ⟨⟨a * h.val * b⁻¹, hd⟩, ?_⟩
    change (QuotientGroup.mk ((a * h.val * b⁻¹) * b) : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup) =
      QuotientGroup.mk a
    rw [eq_comm, QuotientGroup.eq]
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h.property
  · rintro ⟨h, rfl⟩
    exact cosetPrime_stabilizer_smul F E L Q h b

omit [FiniteDimensional F E] in
lemma cosetPrime_mem_primesOver (L : IntermediateField F E) (P : Ideal (𝓞 F))
    (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver P]
    (a : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup) :
    cosetPrime F E L Q a ∈ Ideal.primesOver P (𝓞 L) := by
  induction a using Quotient.inductionOn
  rename_i a
  change (a⁻¹ • Q).under (𝓞 L) ∈ _
  let : (a⁻¹ • Q).IsPrime := Ideal.IsPrime.smul _
  let : (a⁻¹ • Q).LiesOver P := Ideal.LiesOver.smul _
  refine ⟨inferInstance, ?_⟩
  constructor
  rw [Ideal.under_under, (a⁻¹ • Q).over_def P]

def primeOfCosetOrbit (L : IntermediateField F E) (P : Ideal (𝓞 F))
    (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver P] :
    MulAction.orbitRel.Quotient (MulAction.stabilizer (E ≃ₐ[F] E) Q)
      ((E ≃ₐ[F] E) ⧸ L.fixingSubgroup) → Ideal.primesOver P (𝓞 L) := by
  refine Quotient.lift (fun a =>
    ⟨cosetPrime F E L Q a, cosetPrime_mem_primesOver F E L P Q a⟩) ?_
  intro a b h
  apply Subtype.ext
  exact (cosetPrime_eq_iff F E L Q a b).mpr h

end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PermutationArtin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module
open scoped NumberField Classical BigOperators
namespace PrimeDegreePackets.GaloisIdealCharacter

section FiniteCharacters
variable (H : Type*) [CommGroup H] [Finite H]

def additiveCharEquiv : AddChar (Additive H) ℂ ≃ (H →* ℂˣ) :=
  AddChar.toMonoidHomEquiv.trans <|
    ((MulEquiv.monoidHomCongrLeft (MulEquiv.multiplicativeAdditive (H := H))).toEquiv).trans
      MonoidHom.toHomUnitsMulEquiv.toEquiv

def complexMulBasis : Basis (H →* ℂˣ) ℂ (H → ℂ) :=
  ((AddChar.complexBasis (Additive H)).map
    (LinearEquiv.funCongrLeft ℂ ℂ Additive.ofMul)).reindex (additiveCharEquiv H)

@[simp] lemma complexMulBasis_apply (χ : H →* ℂˣ) (h : H) :
    complexMulBasis H χ h = (χ h : ℂ) := by
  simp [complexMulBasis, additiveCharEquiv]

end FiniteCharacters

section OrbitFunctions
variable (C X : Type*) [CommGroup C] [Finite C] [MulAction C X] [Finite X]
local notation "Ω" => MulAction.orbitRel.Quotient C X
abbrev orbitQuotient (o : Ω) := C ⧸ MulAction.stabilizer C o.out
local notation "H" => orbitQuotient C X
local instance permutationArtinOrbitFintype : Fintype Ω := Fintype.ofFinite _
local instance permutationArtinCharacterFintype (o : Ω) : Fintype (H o →* ℂˣ) :=
  Fintype.ofFinite _

def orbitFunctionEquiv : (X → ℂ) ≃ₗ[ℂ] ((o : Ω) → H o → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ
    (MulAction.selfEquivSigmaOrbitsQuotientStabilizer C X).symm).trans
    (LinearEquiv.piCurry ℂ (fun (o : Ω) (_ : H o) => ℂ))

omit [Finite C] [Finite X] in
@[simp] lemma orbitFunctionEquiv_apply (f : X → ℂ) (o : Ω) (h : H o) :
    orbitFunctionEquiv C X f o h = f (MulAction.ofQuotientStabilizer C o.out h) := by
  rfl

def orbitCharacterBasis : Basis ((o : Ω) × (H o →* ℂˣ)) ℂ ((o : Ω) → H o → ℂ) :=
  Pi.basis (fun o => complexMulBasis (H o))

end OrbitFunctions



end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_PermutationEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Permutation characters and local Euler determinants

The permutation representation on the group algebra and the translation
operator on functions have conjugate matrices. This connects the cyclic
induction identities to the actual Frobenius Euler determinants.
-/

noncomputable section
open scoped BigOperators Classical

namespace DukePrimeDegree

def permutationFunctionEquiv (X : Type*) [Finite X] :
    MonoidAlgebra ℂ X ≃ₗ[ℂ] (X → ℂ) :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).trans (Finsupp.linearEquivFunOnFinite ℂ ℂ X)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_SplitEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module NumberField Filter Topology
open scoped NumberField nonZeroDivisors Classical BigOperators
namespace PrimeDegreePackets

lemma mem_idealsOverPrime_iff (K : Type*) [Field K] [NumberField K]
    {p : ℕ} (hp : p ≠ 0) (P : Ideal (𝓞 K)) :
    P ∈ idealsOverPrime K p ↔ P.IsPrime ∧ (p : 𝓞 K) ∈ P := by
  have hspan : (Ideal.span {(p : 𝓞 K)}) ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] using hp
  rw [idealsOverPrime, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hspan,
    Ideal.span_singleton_le_iff_mem]

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ArtinSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical
namespace PrimeDegreePackets.GaloisIdealCharacter
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

def badRationalPrimes (N : ℕ) : Finset Nat.Primes := N.primeFactors.subtype Nat.Prime

end PrimeDegreePackets.GaloisIdealCharacter

namespace PrimeDegreePackets.GaloisIdealCharacter
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
namespace ArtinSeries

variable [IsCyclic (E ≃ₐ[F] E)]
attribute [local instance] IsCyclic.commGroup
local instance instFintypeMonoidHomAlgEquivUnitsComplex_solutions : Fintype ((E ≃ₐ[F] E) →* ℂˣ) := Fintype.ofFinite _

end ArtinSeries
end PrimeDegreePackets.GaloisIdealCharacter

namespace PrimeDegreePackets.GaloisIdealCharacter
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [IsCyclic (E ≃ₐ[F] E)]
attribute [local instance] IsCyclic.commGroup
local instance artinSeriesCharacterFintype : Fintype ((E ≃ₐ[F] E) →* ℂˣ) := Fintype.ofFinite _



end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CosetMeromorphic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module Filter Topology
open scoped NumberField Classical BigOperators
namespace PrimeDegreePackets.GaloisIdealCharacter

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

 
def rationalPrimeSpectrum (p : Nat.Primes) (P : idealsOverPrime F p.val) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 F) := by
  have hP := (mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property
  refine ⟨P.val, hP.1, ?_⟩
  intro he
  rw [he, Ideal.mem_bot] at hP
  exact p.property.ne_zero (Nat.cast_eq_zero.mp hP.2)



section EulerCorrection
variable (K : Type*) [Field K] [NumberField K]

 

def removedEulerPolynomial (N : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ badRationalPrimes N, ∏ P : idealsOverPrime K p.val,
    (1 - (Ideal.absNorm P.val : ℂ)^(-s))

end EulerCorrection

open HeckeMellin
section ContinuedCoset
variable {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]



def cosetXiFactor (N : ℕ) (s : ℂ) : ℂ :=
  removedEulerPolynomial K N s *
    (completionExponential (d+1) |(NumberField.discr K : ℝ)| s)⁻¹ *
    ((Complex.Gamma (s/2))⁻¹)^(d+1) / s / (s-1)

end ContinuedCoset



end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_CyclicContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Continued cyclic Artin factorizations

After realizing the nonprincipal cyclic characters as even ray
characters, the actual Artin factorization continues away from zero and
one. Its zero-order relation has nonnegative finite summands.
-/

noncomputable section

open Filter Set Module
open scoped NumberField BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter
  PrimeDegreePackets.HeckeMellin

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [NumberField.IsTotallyReal F] [NumberField.IsTotallyReal E]
variable {d e N : ℕ} [NeZero N]

section Cyclic

variable [IsCyclic (E ≃ₐ[F] E)]
attribute [local instance] IsCyclic.commGroup
local instance instFintypeMonoidHomAlgEquivUnitsComplex_solutions : Fintype ((E ≃ₐ[F] E) →* ℂˣ) := Fintype.ofFinite _

end Cyclic
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_CyclicRealCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Real characters at a simple real zero

The actual Frobenius ideal character commutes with complex conjugation.
Uniqueness of the entire nonprincipal Hecke continuation therefore makes
the cyclic zero orders conjugation invariant. At a simple real zero the
unique contributing character is real-valued.
-/

noncomputable section
open scoped NumberField BigOperators Classical
open Module

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter
  PrimeDegreePackets.HeckeMellin

@[simp] theorem conjugateLinearCharacter_conjugate {C : Type*} [Group C]
    (χ : C →* ℂˣ) :
    conjugateLinearCharacter (conjugateLinearCharacter χ) = χ := by
  ext g
  simp only [conjugateLinearCharacter_apply, starRingEnd_apply, star_star]

@[simp] theorem conjugateLinearCharacter_one {C : Type*} [Group C] :
    conjugateLinearCharacter (1 : C →* ℂˣ) = 1 := by
  ext g
  simp [conjugateLinearCharacter]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_CyclicSubfields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cyclic subfield factors

For an intermediate field in a cyclic extension, the incomplete zeta
function is the product of exactly those Hecke factors whose characters
are trivial on the fixing subgroup. These subfield orders determine the
real character selected by a simple zero, without general Artin induction.
-/

noncomputable section
open Module Filter Set
open scoped NumberField BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter
  PrimeDegreePackets.HeckeMellin

section Quotient

variable {C : Type*} [CommGroup C] [Finite C]
local instance instFintypeMonoidHomQuotientSubgroupUnitsComplex_solutions (D : Subgroup C) : Fintype (C ⧸ D →* ℂˣ) := Fintype.ofFinite _

end Quotient

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [IsCyclic (E ≃ₐ[F] E)]
attribute [local instance] IsCyclic.commGroup
local instance instFintypeMonoidHomQuotientAlgEquivSubgroupFixingSubgroupUnitsComplex_solutions (L : IntermediateField F E) :
    Fintype ((E ≃ₐ[F] E) ⧸ L.fixingSubgroup →* ℂˣ) := Fintype.ofFinite _

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_ZetaOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A choice-independent continued zeta order

Zero orders do not depend on the ordering of the real embeddings or on
the finite set of removed Euler factors. We fix one ordering only to
package the continued zeta order as a function of a number field.
-/

noncomputable section
open Filter Set Module
open scoped NumberField Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter
  PrimeDegreePackets.HeckeMellin

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

def degreePred (K : Type*) [Field K] [NumberField K] : ℕ := finrank ℚ K - 1

theorem degreePred_spec (K : Type*) [Field K] [NumberField K] :
    finrank ℚ K = degreePred K + 1 := by
  have h : 0 < finrank ℚ K := finrank_pos
  dsimp only [degreePred]
  omega

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_ConjugateSubfields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conjugate subfields have the same zeta zero order

Conjugate subgroups have the same permutation character. The
character-to-Euler identity identifies their actual incomplete Dedekind
zeta functions, and analytic continuation identifies their zero orders.
-/

noncomputable section
open Module Filter Set
open scoped NumberField BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter
  PrimeDegreePackets.HeckeMellin

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
local instance instFintypeAlgEquiv_solutions : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_CyclicGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gluing the real characters selected by a simple zeta zero

A zero-order function on subgroups determines each cyclic restriction by
its values on the subgroups generated by single elements. Conjugacy of
these orders then gives precisely the class function used in odd-degree
descent. No global irreducible-character decomposition is needed.
-/

noncomputable section
open scoped BigOperators Classical

namespace DukePrimeDegree

variable {G : Type*} [Group G] [Finite G]

/-- The sign detected by the zero order of the cyclic fixed field. -/
def cyclicZeroSign (m : Subgroup G → ℤ) (g : G) : ℝˣ :=
  if m (Subgroup.zpowers g) = 1 then 1 else -1

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_SubfieldOrders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer zero orders of fixed fields

The actual continued Dedekind zeta functions have finite nonnegative
orders at real points between zero and one. Permutation character
identities therefore give ordinary integer relations on these orders.
-/

noncomputable section
open scoped NumberField BigOperators Classical

namespace DukePrimeDegree

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [NumberField.IsTotallyReal E]
local instance instFintypeAlgEquiv_solutions_2 : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _
local instance instIsTotallyRealSubtypeMemIntermediateFieldFixedField_solutions (H : Subgroup (E ≃ₐ[F] E)) :
    NumberField.IsTotallyReal (IntermediateField.fixedField H) :=
  NumberField.IsTotallyReal.of_algebra _ E

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_CyclicIntegerOrders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer fixed-field orders at a simple cyclic zero

For a cyclic extension with the actual even ray realizations, a simple
zero selects one real character. Every intermediate-field zero order is
the indicator that this character is trivial on the fixing subgroup.
-/

noncomputable section
open Module
open scoped NumberField BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [IsCyclic (E ≃ₐ[F] E)] [NumberField.IsTotallyReal F] [NumberField.IsTotallyReal E]
local instance instFintypeMonoidHomAlgEquivUnitsComplex_solutions_1 : Fintype ((E ≃ₐ[F] E) →* ℂˣ) := Fintype.ofFinite _
local instance instIsTotallyRealSubtypeMemIntermediateField_solutions (L : IntermediateField F E) : NumberField.IsTotallyReal L :=
  NumberField.IsTotallyReal.of_algebra _ E

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_StarkAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recovering the fixed-field zero order from cyclic averages

This is the scalar form of Stark's descent: the same cyclic indicator
coefficients recover both a class-function average and the zero order of
the corresponding fixed-field zeta function.
-/

noncomputable section
open scoped BigOperators Classical NumberField

namespace DukePrimeDegree

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [NumberField.IsTotallyReal E]
local instance instFintypeAlgEquiv_solutions_3 : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_ZeroPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Propagating a zero to the normal closure

Cyclic factorization gives nonnegative upper bounds for the fixed-field
multiplicities. Cyclic induction then shows that a zero of any fixed
field forces a zero of the full extension. This avoids an assumption of
holomorphy for a general Artin quotient.
-/

noncomputable section
open scoped NumberField BigOperators Classical

namespace DukePrimeDegree

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [NumberField.IsTotallyReal E]
local instance zeroPropagationFintype : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_StarkDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Odd-index descent of a simple zero

Cyclic Hecke factorizations supply the real characters used by Stark's
odd-degree argument. The zero order on any fixed field is an average of
signs and is therefore at most one. A positive order at an odd-index
subgroup is incompatible with a nonvanishing rational zeta function.
-/

noncomputable section
open scoped NumberField BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

variable {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E]
variable [NumberField.IsTotallyReal E]
local instance starkDescentFintype : Fintype (E ≃ₐ[ℚ] E) := Fintype.ofFinite _

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockDiagonalAlgebra
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The algebra of scalars on root blocks

For a partition of the coordinate indices, the block-scalar algebra is
the actual diagonal matrix algebra whose diagonal is constant on each
block. Its dimension is the number of blocks. It is also the common
centralizer of the full diagonal algebra and the elementary root
matrices within the blocks. These are algebraic statements, without
any homogeneous-measure classification assumption.
-/

noncomputable section
open Matrix
open scoped Classical

namespace DukePrimeDegree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal representation of functions on the coordinate blocks. -/
def blockScalarAlgHom (r : Setoid ι) :
    (Quotient r → ℝ) →ₐ[ℝ] Matrix ι ι ℝ where
  toFun c := Matrix.diagonal (fun i => c (Quotient.mk r i))
  map_zero' := by ext i j; simp
  map_one' := by ext i j; simp [Matrix.one_apply]
  map_add' a b := (Matrix.diagonal_add _ _).symm
  map_mul' := by
    intro a b
    rw [Matrix.diagonal_mul_diagonal]
    rfl
  commutes' := by intro c; rfl

@[simp] lemma blockScalarAlgHom_apply (r : Setoid ι) (c : Quotient r → ℝ) :
    blockScalarAlgHom r c = Matrix.diagonal (fun i => c (Quotient.mk r i)) := rfl

/-- The real algebra of diagonal matrices constant on each root block. -/
def blockScalarAlgebra (r : Setoid ι) : Subalgebra ℝ (Matrix ι ι ℝ) :=
  (blockScalarAlgHom r).range

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_PrimeBlockRationality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational diagonal stabilizers of actual lattices

The rational coordinate space below is constructed from an actual lattice
matrix. Its diagonal stabilizer is a concrete subalgebra of real coordinate
functions, not a separately assumed field action. The absence of lattice
vectors on coordinate hyperplanes makes this algebra a field of degree
dividing the ambient dimension.
-/

noncomputable section
open Matrix Module Set
open scoped BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- Rational linear combinations of the rows of a real lattice matrix. -/
def rationalRowMap {n : ℕ} (g : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℝ) where
  toFun z := ∑ i, z i • g i
  map_add' z w := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a z := by
    simp only [RingHom.id_apply, Pi.smul_apply, Finset.smul_sum, smul_smul, smul_eq_mul]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RationalCentralizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rationality of matrix centralizers

The commutant of a finite collection of rational matrices is spanned over
the reals by its rational matrices. This is the linear algebra part of
the homogeneous-orbit rationality step: it uses exactness of scalar
extension, and does not assert that a lattice stabilizer is dense in a
block group.
-/

noncomputable section
open Matrix Module Set
open scoped Classical

namespace DukePrimeDegree

section Matrices

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise rational-to-real scalar extension for matrices. -/
def rationalMatrixCast : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℝ :=
  (Algebra.ofId ℚ ℝ).mapMatrix.toLinearMap

@[simp] lemma rationalMatrixCast_apply (M : Matrix ι ι ℚ) (i j : ι) :
    rationalMatrixCast M i j = (M i j : ℝ) := rfl

/-- The equations for commuting with every member of a matrix family. -/
def commutatorFamily {K : Type*} [Field K] (B : κ → Matrix ι ι K) :
    Matrix ι ι K →ₗ[K] (κ → Matrix ι ι K) :=
  LinearMap.pi fun k => LinearMap.mulRight K (B k) - LinearMap.mulLeft K (B k)

@[simp] lemma commutatorFamily_apply {K : Type*} [Field K]
    (B : κ → Matrix ι ι K) (M : Matrix ι ι K) (k : κ) :
    commutatorFamily B M k = M * B k - B k * M := rfl

end Matrices

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_MatrixConjugationDensity
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite measures in the matrix conjugation representation

This is the elementary recurrence part of the needed Borel-density
argument. A finite measure invariant under a strict real contraction is
concentrated at zero. Applied to matrix coefficients, split diagonal
conjugation forces invariant finite matrix measures onto diagonal matrices.
-/

noncomputable section
open MeasureTheory Filter Set Matrix
open scoped Topology

namespace DukePrimeDegree

/-- Conjugation by a root unipotent matrix. -/
def rootMatrixConjugation {n : ℕ} (i j : Fin n) (t : ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.transvection i j t * M * Matrix.transvection i j (-t)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockNormalizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The connected normalizer of the block algebra

Conjugation permutes the primitive block projections. In a connected
family starting at the identity these projections cannot move, since
their diagonal coordinates remain idempotents. Consequently the identity
component of the block-algebra normalizer preserves every block.
-/

noncomputable section
open Matrix Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def blockProjection {n : ℕ} (r : Setoid (Fin n)) (k : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  blockScalarAlgHom r (fun q => if q = Quotient.mk r k then 1 else 0)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootCurveExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Extracting a root from a differentiable curve

A diagonal with a unique maximal root rescales a curve at the identity.
Its limit is the elementary matrix given by that root component of the
velocity. Closedness then puts this actual root element in the subgroup.
This is a direct matrix argument, with no Lie-subgroup classification.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def rootIsolationWeights {n : ℕ} (i j : Fin n) (a : Fin n) : ℝ :=
  (if a = i then 1 else 0) - (if a = j then 1 else 0)

lemma rootIsolationWeights_sum {n : ℕ} (i j : Fin n) :
    ∑ a, rootIsolationWeights i j a = 0 := by
  simp [rootIsolationWeights, Finset.sum_sub_distrib]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockEliminationSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A full within-block elimination schedule

Upper entries are cleared in increasing row order, and lower entries
in decreasing row order. Transitivity of the block relation ensures
that each affected earlier entry has an earlier zero source entry.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def blockUpperEntries {n : ℕ} (r : Setoid (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ r p.1 p.2)

def blockLowerEntries {n : ℕ} (r : Setoid (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.2 < p.1 ∧ r p.1 p.2)

def blockOffDiagonalEntries {n : ℕ} (r : Setoid (Fin n)) : Finset (Fin n × Fin n) :=
  blockUpperEntries r ∪ blockLowerEntries r

@[simp] lemma mem_blockUpperEntries {n : ℕ} (r : Setoid (Fin n)) (p : Fin n × Fin n) :
    p ∈ blockUpperEntries r ↔ p.1 < p.2 ∧ r p.1 p.2 := by
  simp [blockUpperEntries]

@[simp] lemma mem_blockLowerEntries {n : ℕ} (r : Setoid (Fin n)) (p : Fin n × Fin n) :
    p ∈ blockLowerEntries r ↔ p.2 < p.1 ∧ r p.1 p.2 := by
  simp [blockLowerEntries]

@[simp] lemma mem_blockOffDiagonalEntries {n : ℕ} (r : Setoid (Fin n))
    (p : Fin n × Fin n) :
    p ∈ blockOffDiagonalEntries r ↔ p.1 ≠ p.2 ∧ r p.1 p.2 := by
  simp only [blockOffDiagonalEntries, Finset.mem_union, mem_blockUpperEntries,
    mem_blockLowerEntries]
  constructor
  · rintro (h | h)
    · exact ⟨ne_of_lt h.1, h.2⟩
    · exact ⟨(ne_of_lt h.1).symm, h.2⟩
  · rintro ⟨hne, hr⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl ⟨h, hr⟩
    · exact Or.inr ⟨h, hr⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace


namespace PrimeDegreePackets

variable {α : Type*} [MeasurableSpace α]

 
def increasingMeasureLimit (ν : ℕ → Measure α) (hν : Monotone ν) : Measure α :=
  Measure.ofMeasurable (fun S _ => ⨆ m, ν m S) (by simp) (by
    intro S hS hdis
    simp_rw [measure_iUnion hdis hS]
    have h := lintegral_iSup (μ := Measure.count)
      (fun m => measurable_of_countable (f := fun k : ℕ => ν m (S k)))
      (show Monotone (fun m k => ν m (S k)) from fun a b hab k => hν hab (S k))
    simpa only [lintegral_count] using h.symm)

lemma increasingMeasureLimit_apply (ν : ℕ → Measure α) (hν : Monotone ν)
    {S : Set α} (hS : MeasurableSet S) :
    increasingMeasureLimit ν hν S = ⨆ m, ν m S :=
  Measure.ofMeasurable_apply S hS

lemma le_increasingMeasureLimit (ν : ℕ → Measure α) (hν : Monotone ν) (m : ℕ) :
    ν m ≤ increasingMeasureLimit ν hν := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [increasingMeasureLimit_apply ν hν hS]
  exact le_iSup (fun j => ν j S) m



lemma restrictionChain_monotone (ν : ℕ → Measure α) (W : ℕ → Set α)
    (hcompat : ∀ a b, a ≤ b → (ν b).restrict (W a) = ν a) : Monotone ν := by
  intro a b hab
  rw [←hcompat a b hab]
  exact Measure.restrict_le_self

 
theorem increasingMeasureLimit_restrict (ν : ℕ → Measure α) (W : ℕ → Set α)
    (hW : ∀ m, MeasurableSet (W m))
    (hcompat : ∀ a b, a ≤ b → (ν b).restrict (W a) = ν a) (m : ℕ) :
    (increasingMeasureLimit ν (restrictionChain_monotone ν W hcompat)).restrict (W m) = ν m := by
  let hν := restrictionChain_monotone ν W hcompat
  apply le_antisymm
  · apply Measure.le_iff.mpr
    intro S hS
    rw [Measure.restrict_apply hS,increasingMeasureLimit_apply ν hν (hS.inter (hW m))]
    apply iSup_le
    intro a
    by_cases ham : a ≤ m
    · exact (hν ham _) |>.trans (measure_mono inter_subset_left)
    · have hm : m ≤ a := le_of_not_ge ham
      have he := congrArg (fun ρ : Measure α => ρ S) (hcompat m a hm)
      simpa only [Measure.restrict_apply hS] using he.le
  · rw [←hcompat m m le_rfl]
    exact Measure.restrict_mono subset_rfl (le_increasingMeasureLimit ν hν m)

 
theorem measure_eq_of_restrictionChain (W : ℕ → Set α)
    (hW : Monotone W) (hcover : ⋃ m, W m = univ)
    (ν ρ : Measure α) (heq : ∀ m, ν.restrict (W m) = ρ.restrict (W m)) : ν = ρ := by
  ext S hS
  have he : S = ⋃ m, S ∩ W m := by rw [←inter_iUnion,hcover,inter_univ]
  rw [he,(show Monotone (fun m => S ∩ W m) from fun a b hab => inter_subset_inter_right S (hW hab)).measure_iUnion,
    (show Monotone (fun m => S ∩ W m) from fun a b hab => inter_subset_inter_right S (hW hab)).measure_iUnion]
  congr 1
  funext m
  simpa only [Measure.restrict_apply hS] using congrArg (fun ξ : Measure α => ξ S) (heq m)

 
theorem increasingMeasureLimit_locallyFinite [TopologicalSpace α]
    (ν : ℕ → Measure α) [∀ m, IsFiniteMeasure (ν m)] (W : ℕ → Set α)
    (hW : ∀ m, IsOpen (W m)) (hWm : ∀ m, MeasurableSet (W m))
    (hcover : ⋃ m, W m = univ)
    (hcompat : ∀ a b, a ≤ b → (ν b).restrict (W a) = ν a) :
    IsLocallyFiniteMeasure (increasingMeasureLimit ν (restrictionChain_monotone ν W hcompat)) := by
  constructor
  intro x
  have hx : x ∈ ⋃ m, W m := by rw [hcover]; trivial
  obtain ⟨m,hm⟩ := mem_iUnion.mp hx
  refine ⟨W m,(hW m).mem_nhds hm,?_⟩
  have H := congrArg (fun ρ : Measure α => ρ univ)
    (increasingMeasureLimit_restrict ν W hWm hcompat m)
  rw [Measure.restrict_apply MeasurableSet.univ,univ_inter] at H
  rw [H]
  exact measure_lt_top _ _

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory


namespace PrimeDegreePackets

lemma measurable_measure_restrict {α : Type*} [MeasurableSpace α]
    {S : Set α} (hS : MeasurableSet S) :
    Measurable (fun ν : Measure α => ν.restrict S) := by
  apply Measure.measurable_of_measurable_coe
  intro T hT
  simp only [Measure.restrict_apply hT]
  exact Measure.measurable_coe (hT.inter hS)

lemma measurable_measure_sum {α : Type*} [MeasurableSpace α] :
    Measurable (fun ν : ℕ → Measure α => Measure.sum ν) := by
  apply Measure.measurable_of_measurable_coe
  intro T hT
  simp only [Measure.sum_apply _ hT]
  exact Measurable.tsum (fun m => (Measure.measurable_coe hT).comp (measurable_pi_apply m))

lemma measure_eq_sum_disjointed {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (W : ℕ → Set α) (hW : ∀ m, MeasurableSet (W m))
    (hcov : ⋃ m, W m = univ) :
    ν = Measure.sum (fun m => ν.restrict (disjointed W m)) := by
  have H := ν.restrict_iUnion (disjoint_disjointed W) (MeasurableSet.disjointed hW)
  rw [iUnion_disjointed,hcov,Measure.restrict_univ] at H
  exact H

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
namespace PrimeDegreePackets

lemma real_mem_measureSupport_iff_rat (ν : Measure ℝ) (t : ℝ) :
    t ∈ ν.support ↔ ∀ a b : ℚ, t ∈ Ioo (a : ℝ) b → 0 < ν (Ioo (a : ℝ) b) := by
  constructor
  · intro ht a b hab
    exact (ν.mem_support_iff_forall t).mp ht _ (isOpen_Ioo.mem_nhds hab)
  · intro ht
    apply (ν.mem_support_iff_forall t).mpr
    intro U hU
    obtain ⟨l,u,htu,hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hU
    obtain ⟨a,hla,hat⟩ := exists_rat_btwn htu.1
    obtain ⟨b,htb,hbu⟩ := exists_rat_btwn htu.2
    exact (ht a b ⟨hat,htb⟩).trans_le (measure_mono (fun x hx => hlu ⟨hla.trans hx.1,hx.2.trans hbu⟩))

 

lemma measurableSet_kernel_support {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) : MeasurableSet {z : α × ℝ | z.2 ∈ (κ z.1).support} := by
  simp_rw [real_mem_measureSupport_iff_rat,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  apply MeasurableSet.iInter
  intro b
  exact (measurable_snd measurableSet_Ioo).imp
    (measurableSet_lt measurable_const ((κ.measurable_coe measurableSet_Ioo).comp measurable_fst))

end PrimeDegreePackets


namespace PrimeDegreePackets



def finiteRealWindows {α : Type*} [MeasurableSpace α] (κ : Kernel α ℝ) : Set α :=
  {a | ∀ m : ℕ, κ a (Icc (-(m : ℝ)) m) < ∞}

lemma measurableSet_finiteRealWindows {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) : MeasurableSet (finiteRealWindows κ) := by
  change MeasurableSet {a | ∀ m : ℕ, κ a (Icc (-(m : ℝ)) m) < ∞}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun m => measurableSet_lt
    (κ.measurable_coe measurableSet_Icc) measurable_const

lemma locallyFinite_of_finite_real_windows (ν : Measure ℝ)
    (hν : ∀ m : ℕ, ν (Icc (-(m : ℝ)) m) < ∞) : IsLocallyFiniteMeasure ν := by
  constructor
  intro t
  obtain ⟨m,hm⟩ := exists_nat_gt |t|
  refine ⟨Ioo (-(m : ℝ)) m,isOpen_Ioo.mem_nhds ⟨?_,?_⟩,?_⟩
  · have := neg_abs_le t
    linarith
  · exact (le_abs_self t).trans_lt hm
  · exact (measure_mono Set.Ioo_subset_Icc_self).trans_lt (hν m)

 
def locallyFiniteRealVersion {α : Type*} [MeasurableSpace α] (κ : Kernel α ℝ) : Kernel α ℝ :=
  Kernel.piecewise (measurableSet_finiteRealWindows κ) κ 0

instance locallyFiniteRealVersion_locallyFinite {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) (a : α) : IsLocallyFiniteMeasure (locallyFiniteRealVersion κ a) := by
  change IsLocallyFiniteMeasure (if a ∈ finiteRealWindows κ then κ a else 0)
  split_ifs with ha
  · exact locallyFinite_of_finite_real_windows (κ a) ha
  · infer_instance

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafAnchors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory


namespace PrimeDegreePackets
variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace δ]

 
def restrictFibers (κ : Kernel α β) [IsSFiniteKernel κ]
    (T : Set (α × β)) (hT : MeasurableSet T) : Kernel α β where
  toFun a := (κ a).restrict (Prod.mk a ⁻¹' T)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    have H := Kernel.measurable_kernel_prodMk_left (κ := κ) ((measurable_snd hS).inter hT)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext a
    exact Measure.restrict_apply hS

instance restrictFibers_finite (κ : Kernel α β) [IsFiniteKernel κ]
    (T : Set (α × β)) (hT : MeasurableSet T) : IsFiniteKernel (restrictFibers κ T hT) := by
  refine ⟨κ.bound,κ.bound_lt_top,fun a => ?_⟩
  change (κ a).restrict (Prod.mk a ⁻¹' T) univ ≤ κ.bound
  exact (Measure.restrict_le_self _).trans (κ.measure_le_bound a univ)

lemma compProd_restrict_fibers (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsFiniteKernel κ] (T : Set (α × β)) (hT : MeasurableSet T) :
    (μ ⊗ₘ κ).restrict T = μ ⊗ₘ restrictFibers κ T hT := by
  ext S hS
  rw [Measure.restrict_apply hS,Measure.compProd_apply (hS.inter hT),Measure.compProd_apply hS]
  apply lintegral_congr
  intro a
  exact (Measure.restrict_apply (measurable_prodMk_left hS)).symm

lemma conditional_restrict_marginal [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (T : Set (α × β)) (hT : MeasurableSet T) :
    (ρ.restrict T).fst = ρ.fst.withDensity (fun a => ρ.condKernel a (Prod.mk a ⁻¹' T)) := by
  have H := compProd_restrict_fibers ρ.fst ρ.condKernel T hT
  rw [Measure.disintegrate] at H
  rw [H,fst_compProd_withDensity]
  congr 1
  funext a
  change (ρ.condKernel a).restrict (Prod.mk a ⁻¹' T) univ = _
  rw [Measure.restrict_apply MeasurableSet.univ,univ_inter]

 

theorem conditional_restrict_fibers [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (T : Set (α × β)) (hT : MeasurableSet T) :
    ∀ᵐ a ∂ρ.fst, ρ.condKernel a (Prod.mk a ⁻¹' T) • (ρ.restrict T).condKernel a =
      (ρ.condKernel a).restrict (Prod.mk a ⁻¹' T) := by
  let σ := ρ.restrict T
  let w := fun a => ρ.condKernel a (Prod.mk a ⁻¹' T)
  have hw : Measurable w := Kernel.measurable_kernel_prodMk_left hT
  let κ := scaleBaseKernel σ.condKernel w hw
  let : IsFiniteKernel κ := scaleBaseKernel_finite σ.condKernel w hw (fun a => prob_le_one)
  have he : ρ.fst ⊗ₘ κ = ρ.fst ⊗ₘ restrictFibers ρ.condKernel T hT := by
    calc
      _ = ρ.fst.withDensity w ⊗ₘ σ.condKernel := compProd_scaleBaseKernel _ _ w hw
      _ = σ.fst ⊗ₘ σ.condKernel := by rw [conditional_restrict_marginal ρ T hT]
      _ = σ := Measure.disintegrate σ σ.condKernel
      _ = ρ.fst ⊗ₘ restrictFibers ρ.condKernel T hT := by
        rw [←compProd_restrict_fibers,Measure.disintegrate]
  exact Kernel.ae_eq_of_compProd_eq he

 

def mapFibers (κ : Kernel α β) [IsSFiniteKernel κ]
    (F : α × β → δ) (hF : Measurable F) : Kernel α δ where
  toFun a := (κ a).map (fun b => F (a,b))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    have H := Kernel.measurable_kernel_prodMk_left (κ := κ) (hF hS)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext a
    exact Measure.map_apply ((show Measurable (fun b => F (a,b)) from hF.comp measurable_prodMk_left)) hS

lemma mapFibers_apply (κ : Kernel α β) [IsSFiniteKernel κ]
    (F : α × β → δ) (hF : Measurable F) (a : α) :
    mapFibers κ F hF a = (κ a).map (fun b => F (a,b)) := rfl

instance mapFibers_finite (κ : Kernel α β) [IsFiniteKernel κ]
    (F : α × β → δ) (hF : Measurable F) : IsFiniteKernel (mapFibers κ F hF) := by
  refine ⟨κ.bound,κ.bound_lt_top,fun a => ?_⟩
  change (κ a).map (fun b => F (a,b)) univ ≤ κ.bound
  rw [Measure.map_apply ((show Measurable (fun b => F (a,b)) from hF.comp measurable_prodMk_left)) MeasurableSet.univ,preimage_univ]
  exact κ.measure_le_bound a univ

lemma fst_map_fibers (ρ : Measure (α × β)) (e : α ≃ᵐ γ)
    (F : α × β → δ) (hF : Measurable F) :
    (ρ.map (fun z => (e z.1,F z))).fst = ρ.fst.map e := by
  have hfull : Measurable (fun z : α × β => (e z.1,F z)) :=
    (e.measurable.comp measurable_fst).prodMk hF
  rw [Measure.fst,Measure.map_map measurable_fst hfull,
    Measure.fst,Measure.map_map e.measurable measurable_fst]
  rfl

lemma compProd_map_fibers (μ : Measure α) [SFinite μ] (κ : Kernel α β)
    [IsFiniteKernel κ] (e : α ≃ᵐ γ) (F : α × β → δ) (hF : Measurable F) :
    (μ ⊗ₘ κ).map (fun z => (e z.1,F z)) =
      μ.map e ⊗ₘ (mapFibers κ F hF).comap e.symm e.symm.measurable := by
  have hfull : Measurable (fun z : α × β => (e z.1,F z)) :=
    (e.measurable.comp measurable_fst).prodMk hF
  ext S hS
  rw [Measure.map_apply hfull hS,Measure.compProd_apply (hfull hS),Measure.compProd_apply hS,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hS) e.measurable]
  apply lintegral_congr
  intro a
  rw [Kernel.comap_apply,e.symm_apply_apply,mapFibers_apply]
  exact (Measure.map_apply ((show Measurable (fun b => F (a,b)) from hF.comp measurable_prodMk_left))
    (show MeasurableSet (Prod.mk (e a) ⁻¹' S) from measurable_prodMk_left hS)).symm

 

theorem conditional_map_fibers [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace δ] [Nonempty δ] (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (e : α ≃ᵐ γ) (F : α × β → δ) (hF : Measurable F) :
    ∀ᵐ a ∂ρ.fst, (ρ.map (fun z => (e z.1,F z))).condKernel (e a) =
      (ρ.condKernel a).map (fun b => F (a,b)) := by
  let κ := (mapFibers ρ.condKernel F hF).comap e.symm e.symm.measurable
  have he : ρ.map (fun z => (e z.1,F z)) = (ρ.map (fun z => (e z.1,F z))).fst ⊗ₘ κ := by
    rw [fst_map_fibers ρ e F hF,←compProd_map_fibers ρ.fst ρ.condKernel e F hF,Measure.disintegrate]
  have H := eq_condKernel_of_measure_eq_compProd κ he
  rw [fst_map_fibers ρ e F hF] at H
  have H' := ae_of_ae_map e.measurable.aemeasurable H
  filter_upwards [H'] with a ha
  exact (by simpa only [κ,Kernel.comap_apply,e.symm_apply_apply,mapFibers_apply] using ha.symm)

end PrimeDegreePackets


namespace PrimeDegreePackets

 
def fiberShear {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) (τ : α → ℝ) (hτ : Continuous τ) : (α × ℝ) ≃ₜ (β × ℝ) where
  toFun z := (e z.1,z.2 + τ z.1)
  invFun z := (e.symm z.1,z.2 - τ (e.symm z.1))
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  continuous_toFun := (e.continuous.comp continuous_fst).prodMk
    (continuous_snd.add (hτ.comp continuous_fst))
  continuous_invFun := (e.symm.continuous.comp continuous_fst).prodMk
    (continuous_snd.sub (hτ.comp (e.symm.continuous.comp continuous_fst)))

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ConditionalFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
namespace PrimeDegreePackets
variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace δ]

lemma fst_map_fibers_of_measurable (ρ : Measure (α × β))
    (e : α → γ) (he : Measurable e) (F : α × β → δ) (hF : Measurable F) :
    (ρ.map (fun z => (e z.1,F z))).fst = ρ.fst.map e := by
  have hfull : Measurable (fun z : α × β => (e z.1,F z)) := (he.comp measurable_fst).prodMk hF
  rw [Measure.fst,Measure.map_map measurable_fst hfull,
    Measure.fst,Measure.map_map he measurable_fst]
  rfl

lemma compProd_map_fibers_leftInverse (μ : Measure α) [SFinite μ] (κ : Kernel α β)
    [IsFiniteKernel κ] (e : α → γ) (he : Measurable e)
    (r : γ → α) (hr : Measurable r) (hre : Function.LeftInverse r e)
    (F : α × β → δ) (hF : Measurable F) :
    (μ ⊗ₘ κ).map (fun z => (e z.1,F z)) =
      μ.map e ⊗ₘ (mapFibers κ F hF).comap r hr := by
  have hfull : Measurable (fun z : α × β => (e z.1,F z)) := (he.comp measurable_fst).prodMk hF
  ext S hS
  rw [Measure.map_apply hfull hS,Measure.compProd_apply (hfull hS),Measure.compProd_apply hS,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hS) he]
  apply lintegral_congr
  intro a
  rw [Kernel.comap_apply,hre a,mapFibers_apply]
  exact (Measure.map_apply (hF.comp measurable_prodMk_left)
    (show MeasurableSet (Prod.mk (e a) ⁻¹' S) from measurable_prodMk_left hS)).symm

lemma conditional_map_fibers_leftInverse [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace δ] [Nonempty δ] (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (e : α → γ) (he : Measurable e) (r : γ → α) (hr : Measurable r)
    (hre : Function.LeftInverse r e) (F : α × β → δ) (hF : Measurable F) :
    ∀ᵐ a ∂ρ.fst, (ρ.map (fun z => (e z.1,F z))).condKernel (e a) =
      (ρ.condKernel a).map (fun b => F (a,b)) := by
  let κ := (mapFibers ρ.condKernel F hF).comap r hr
  have heq : ρ.map (fun z => (e z.1,F z)) = (ρ.map (fun z => (e z.1,F z))).fst ⊗ₘ κ := by
    rw [fst_map_fibers_of_measurable ρ e he F hF,
      ←compProd_map_fibers_leftInverse ρ.fst ρ.condKernel e he r hr hre F hF,
      Measure.disintegrate]
  have H := eq_condKernel_of_measure_eq_compProd κ heq
  rw [fst_map_fibers_of_measurable ρ e he F hF] at H
  have H' := ae_of_ae_map he.aemeasurable H
  filter_upwards [H'] with a ha
  simpa only [κ,Kernel.comap_apply,hre a,mapFibers_apply] using ha.symm

 

theorem conditional_map_fibers_embedding [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace δ] [Nonempty δ] (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (e : α → γ) (he : MeasurableEmbedding e) (F : α × β → δ) (hF : Measurable F) :
    ∀ᵐ a ∂ρ.fst, (ρ.map (fun z => (e z.1,F z))).condKernel (e a) =
      (ρ.condKernel a).map (fun b => F (a,b)) := by
  cases isEmpty_or_nonempty α with
  | inl h => exact ae_of_all _ (fun a => isEmptyElim a)
  | inr h =>
    exact conditional_map_fibers_leftInverse ρ e he.measurable he.invFun
      he.measurable_invFun he.leftInverse_invFun F hF

end PrimeDegreePackets


namespace PrimeDegreePackets
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

abbrev baseSubtypeMap (U : Set α) : U × β → α × β := fun z => (z.1.val,z.2)

lemma baseSubtypeMap_embedding (U : Set α) (hU : MeasurableSet U) :
    MeasurableEmbedding (baseSubtypeMap (β := β) U) :=
  (MeasurableEmbedding.subtype_coe hU).prodMap MeasurableEmbedding.id

omit [MeasurableSpace α] [MeasurableSpace β] in
lemma baseSubtypeMap_range (U : Set α) :
    Set.range (baseSubtypeMap (β := β) U) = U ×ˢ univ := by
  ext z
  simp only [Set.mem_range,Set.mem_prod,Set.mem_univ,and_true]
  constructor
  · rintro ⟨x,rfl⟩; exact x.1.prop
  · intro hz; exact ⟨(⟨z.1,hz⟩,z.2),Prod.ext rfl rfl⟩

lemma map_comap_baseSubtype (ρ : Measure (α × β)) (U : Set α) (hU : MeasurableSet U) :
    (ρ.comap (baseSubtypeMap U)).map (baseSubtypeMap U) = ρ.restrict (U ×ˢ univ) := by
  rw [(baseSubtypeMap_embedding U hU).map_comap,baseSubtypeMap_range]

lemma fst_map_comap_baseSubtype [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (U : Set α) (hU : MeasurableSet U) :
    ((ρ.comap (baseSubtypeMap U)).fst).map Subtype.val = ρ.fst.restrict U := by
  rw [←fst_map_fibers_of_measurable _ Subtype.val measurable_subtype_coe Prod.snd measurable_snd]
  change ((ρ.comap (baseSubtypeMap U)).map (baseSubtypeMap U)).fst = _
  rw [map_comap_baseSubtype ρ U hU,restricted_conditional_marginal ρ hU MeasurableSet.univ]
  simp only [measure_univ]
  exact MeasureTheory.withDensity_one

theorem conditional_comap_baseSubtype [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (U : Set α) (hU : MeasurableSet U) :
    ∀ᵐ a ∂(ρ.comap (baseSubtypeMap U)).fst,
      (ρ.comap (baseSubtypeMap U)).condKernel a = ρ.condKernel a.val := by
  have H₁ := conditional_map_fibers_embedding (ρ.comap (baseSubtypeMap U))
    Subtype.val (MeasurableEmbedding.subtype_coe hU) Prod.snd measurable_snd
  have he : (ρ.comap (baseSubtypeMap U)).map (fun z => (z.1.val,Prod.snd z)) =
      ρ.restrict (U ×ˢ univ) := map_comap_baseSubtype ρ U hU
  have H₂ : ∀ᵐ a ∂ρ.fst.restrict U,
      (ρ.restrict (U ×ˢ univ)).condKernel a = ρ.condKernel a := by
    filter_upwards [restricted_conditional_kernel ρ hU MeasurableSet.univ] with a ha
    simpa only [measure_univ,one_smul,Measure.restrict_univ] using ha
  rw [←fst_map_comap_baseSubtype ρ U hU] at H₂
  have H₂' := ae_of_ae_map measurable_subtype_coe.aemeasurable H₂
  filter_upwards [H₁,H₂'] with a ha hb
  simp only [he] at ha
  exact (Measure.map_id (μ := (ρ.comap (baseSubtypeMap U)).condKernel a)).symm.trans
    (ha.symm.trans hb)

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma fst_restrict_base {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure (α × β)) {U : Set α} (hU : MeasurableSet U) :
    (ρ.restrict (Prod.fst ⁻¹' U)).fst = ρ.fst.restrict U := by
  exact (Measure.restrict_map measurable_fst hU).symm

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntrinsicLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal


namespace PrimeDegreePackets

lemma realScaling_preimage_ball (c r : ℝ) (hc : 0 < c) :
    (Homeomorph.mulLeft₀ c hc.ne') ⁻¹' Metric.ball (0:ℝ) r = Metric.ball 0 (r/c) := by
  ext x
  simp only [Set.mem_preimage,Metric.mem_ball,Homeomorph.coe_mulLeft₀,Real.dist_eq,sub_zero]
  rw [abs_mul,abs_of_pos hc]
  rw [lt_div_iff₀ hc,mul_comm c]

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafPeriods
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
namespace PrimeDegreePackets

 
def realLeafPeriods (ν : Measure ℝ) : AddSubgroup ℝ where
  carrier := {a | ν.map (fun x => x+a) = ν}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change ν.map (fun x => x+(a+b)) = ν
    have H : (fun x : ℝ => x+(a+b)) = (fun x => x+b) ∘ (fun x => x+a) := by
      ext x
      simp only [Function.comp_apply,add_assoc]
    rw [H,←Measure.map_map (by fun_prop) (by fun_prop),ha,hb]
  neg_mem' := by
    intro a ha
    change ν.map (fun x => x + -a) = ν
    have H := congrArg (fun ρ : Measure ℝ => ρ.map (fun x => x + -a)) ha
    rw [Measure.map_map (by fun_prop) (by fun_prop)] at H
    simpa only [Function.comp_def,add_neg_cancel_right,Measure.map_id'] using H.symm

@[simp] lemma mem_realLeafPeriods (ν : Measure ℝ) (a : ℝ) :
    a ∈ realLeafPeriods ν ↔ ν.map (fun x => x+a) = ν := Iff.rfl

end PrimeDegreePackets


namespace PrimeDegreePackets

abbrev leafTestSpace (N : ℕ) :=
  {f : C(ℝ,ℝ) // ∀ x : ℝ, x ∉ Icc (-(N:ℝ)) N → f x = 0}

instance instSecondCountableTopologyLeafTestSpace (N : ℕ) : SecondCountableTopology (leafTestSpace N) :=
  Subtype.secondCountableTopology
    (s := {f : C(ℝ,ℝ) | ∀ x : ℝ, x ∉ Icc (-(N:ℝ)) N → f x = 0})

instance instNonemptyLeafTestSpace (N : ℕ) : Nonempty (leafTestSpace N) := ⟨⟨0,fun _ _ => rfl⟩⟩

 
def leafTest (N k : ℕ) : C_c(ℝ,ℝ) :=
  ⟨(denseSeq (leafTestSpace N) k).val,
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal (by
        intro x hx
        by_contra h
        exact hx ((denseSeq (leafTestSpace N) k).prop x h)) isClosed_Icc)⟩

end PrimeDegreePackets


namespace PrimeDegreePackets


def hasSmallLeafPeriod (ν : Measure ℝ) (R : ℝ) : Prop :=
  ∃ a : ℝ, a ∈ realLeafPeriods ν ∧ 0 < a ∧ a ≤ R

end PrimeDegreePackets

open MeasureTheory Set Filter TopologicalSpace
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ScalingCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory


namespace PrimeDegreePackets

def rootCanonicalWeights (d : ℕ) (j : Fin (d+1)) (k : Fin (d+1)) : ℝ :=
  coordinateContractionWeights d j k / (d+1:ℝ)

lemma rootCanonicalWeights_sum (d : ℕ) (j : Fin (d+1)) :
    ∑ k, rootCanonicalWeights d j k = 0 := by
  simp only [rootCanonicalWeights,←Finset.sum_div,coordinateContractionWeights_sum,zero_div]

lemma rootCanonicalWeights_difference (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j) :
    rootCanonicalWeights d j j - rootCanonicalWeights d j i = 1 := by
  simp only [rootCanonicalWeights,←sub_div]
  have h : coordinateContractionWeights d j j - coordinateContractionWeights d j i = (d+1:ℝ) := by
    simp [coordinateContractionWeights,hij]
  rw [h,div_self (by positivity)]

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootInvariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace


namespace PrimeDegreePackets


def projectiveLeafPeriod (ν : Measure ℝ) (p : ℝ × ℝ) : Prop :=
  ν.map (fun x => x+p.1) = ENNReal.ofReal (Real.exp p.2) • ν

end PrimeDegreePackets


namespace PrimeDegreePackets



def boundedProjectiveLeafPeriod (ν : Measure ℝ) (R l u : ℝ) : Prop :=
  ∃ p : ℝ × ℝ, projectiveLeafPeriod ν p ∧ |p.1| ≤ R ∧ p.2 ∈ Icc l u

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_SpectralSeparation
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The spectral estimate for exceptional returns

EKL (2006), Lemma 5.3, in the form needed for real diagonal return
matrices. A fixed neighborhood of the identity works for every set of
logarithmic diagonal weights separated by more than one.
-/

noncomputable section
open Set Matrix
open scoped BigOperators Classical

namespace DukePrimeDegree

/-- Uniform relative error allowed by half-unit logarithmic brackets. -/
def spectralRelativeRadius : ℝ := 1 - Real.exp (-(1 / 2 : ℝ))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CentralizerWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# An explicit neutral direction excluding centralizer orbits

The two root coordinates receive the same negative weight. The remaining
coordinates receive distinct positive weights. Their sum is balanced by
the repeated negative weight. This discharges the elementary weight
conditions in the centralizer-orbit exclusion.
-/

noncomputable section
open Set MeasureTheory Matrix
open scoped Classical Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def centralizerWitnessWeights {n m : ℕ} (e : Fin n ≃ Fin 2 ⊕ Fin m) : Fin n → ℝ :=
  fun i => Sum.elim (fun _ : Fin 2 => -(∑ r : Fin m, ((r : ℝ) + 1)) / 2)
    (fun r : Fin m => (r : ℝ) + 1) (e i)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ErgodicAverageMean
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Identifying the constant ergodic average

The constant obtained from the L2 mean ergodic theorem is the integral
of the original observable. Integration is represented by pairing with
the constant-one vector, so passage to the limit is continuous in L2.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace DukePrimeDegree

variable {X : Type*} [MeasurableSpace X]

/-- Constant observables as actual L2 vectors. -/
def constantL2 (μ : Measure X) [IsFiniteMeasure μ] (c : ℝ) : Lp ℝ 2 μ :=
  (memLp_const c : MemLp (fun _ : X => c) 2 μ).toLp (fun _ => c)

/-- Integration is the continuous L2 pairing with the constant one. -/
def meanL2 (μ : Measure X) [IsFiniteMeasure μ] : Lp ℝ 2 μ →L[ℝ] ℝ :=
  innerSL ℝ (constantL2 μ 1)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_OrbitCoboundary
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded coboundary approximations to an orbit observable

The difference between a bounded observable and any one of its finite
orbit averages is an explicit bounded coboundary. This is the uniform
part of the maximal-inequality proof of a common generic set.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree

variable {X : Type*}

def orbitAveragePotential (T : X → X) (f : X → ℝ) (M : ℕ) (x : X) : ℝ :=
  (M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, birkhoffSum T f j x

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_HopfMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite maximal ergodic inequality

The maximal recurrence estimate used in EKL (2006), Section 4.3, follows
from this elementary finite Hopf inequality. The running maximum is built
recursively, so its integrability and its coboundary bound require no
pointwise ergodic theorem.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree

def positiveRunningSum {Y : Type*} (T : Y → Y) (f : Y → ℝ) : ℕ → Y → ℝ
  | 0 => 0
  | n + 1 => fun x => max 0 (f x + positiveRunningSum T f n (T x))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_FlowWindowAverages
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unit smoothing and continuous orbit windows

Discrete averages of a unit-smoothed observable are exactly continuous
flow averages at integer lengths. Shifting the initial point changes
only two boundary intervals; their contribution is uniformly bounded.
Neither statement assumes that a time-one map is ergodic.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree

variable {X : Type*}

def unitFlowSmooth (U : ℝ → X → X) (f : X → ℝ) (x : X) : ℝ :=
  ∫ t in (0 : ℝ)..1, f (U t x)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_FlowSmoothedL2
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean convergence for a real flow without time-one ergodicity

Unit smoothing removes the possible nonconstant time-one invariant
vectors. The boundary estimate makes the Hilbert-space limit invariant
under every real time, and ergodicity of the entire flow then makes it
constant. This is the averaging statement needed on actual ergodic
components of a root flow.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree

variable {X : Type*} [MulAction (Multiplicative ℝ) X]

def realActionTime (s : ℝ) (x : X) : X := Multiplicative.ofAdd s • x

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CompactFamilyGeneric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A fixed generic set for a compact family of observables

The limiting shear is selected after the generic set. Compactness of the
possible shears gives a compact family of translated observables in the
uniform norm. A finite approximation therefore suffices for one common
generic set and time threshold. No commutation of the translating group
with the averaging flow is required.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace DukePrimeDegree

def compactObservableTranslate
    {H Y : Type*} [Group H] [TopologicalSpace H] [TopologicalSpace Y]
    [MulAction H Y] [ContinuousSMul H Y]
    (f : CompactlySupportedContinuousMap Y ℝ) (a : H) : Y →ᵇ ℝ :=
  f.toBoundedContinuousFunction.compContinuous ⟨fun x => a • x, continuous_const_smul a⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_DiagonalRecurrence
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vanishing of expanding scalar coordinates in a finite invariant law

This is the scalar step in diagonal recurrence on projective or
Grassmannian coordinates. Bounded monotone truncation avoids assuming
that the original coordinate is integrable. It will be applied to ratios
of unequal diagonal weights; no stabilizer or orbit conclusion is assumed.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace DukePrimeDegree

def boundedAbsCoordinate (x : ℝ) : ℝ := |x| / (1 + |x|)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_EntropyInverse
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Time reversal of entropy

Reversing a finite orbit name and shifting its starting point does not
change its Shannon entropy. This proves equality of
Kolmogorov--Sinai entropy for mutually inverse measure-preserving maps,
as used in EKL (2006), equation (3.2).
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

/-- Reversal is a permutation of the finite word alphabet. -/
def reverseWordEquiv (α : Type*) (N : ℕ) : (Fin N → α) ≃ (Fin N → α) where
  toFun w j := w j.rev
  invFun w j := w j.rev
  left_inv w := by funext j; simp
  right_inv w := by funext j; simp

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_FlowOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One-unit occupation observables

For a measurable measure-preserving flow, the time spent in a measurable
set during one unit interval is a measurable integrable observable. Its
space integral is exactly the measure of that set. Its discrete sums
are the occupation integrals on the corresponding integer intervals.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree

def unitFlowOccupation {Y : Type*} (Φ : ℝ → Y → Y) (E : Set Y) (x : Y) : ℝ :=
  ∫ t in Ioc (0 : ℝ) 1, E.indicator (fun _ => (1 : ℝ)) (Φ t x)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The two-coordinate shearing diagonal

In the row-lattice convention the weights are `-1` at the root's row,
`+1` at its column, and zero elsewhere. Backward right translation
contracts root time by `exp (-2*t)`. The corresponding relative return
matrix has a fixed diagonal difference, quadratic coefficient growing
by `exp (2*t)`, and other shearing coefficients growing by `exp t`.
These are the rates in EKL (2006), Lemma 4.6.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

def rootPairWeights {n : ℕ} (i j : Fin n) (k : Fin n) : ℝ :=
  (if k = j then 1 else 0) - (if k = i then 1 else 0)

lemma rootPairWeights_sum {n : ℕ} (i j : Fin n) : ∑ k, rootPairWeights i j k = 0 := by
  simp [rootPairWeights, Finset.sum_sub_distrib]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_LeafFlowCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Joint almost-everywhere leaf covariance for the shearing flow

The fixed-time covariance theorem alone does not justify using a time
selected from a recurrence argument. Measurable kernels and a countable
determining family of leaf tests allow Fubini to put the time quantifier
inside: almost every initial point has covariance at almost every real
time. This is sufficient for selection after finitely many affine time
changes, without asserting an unproved pointwise equivariant version.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rescaledRealKernel {Y : Type*} [MeasurableSpace Y]
    (κ : Kernel Y ℝ) [IsSFiniteKernel κ] (c : Y → ℝ) (hc : Measurable c) :
    Kernel Y ℝ where
  toFun y := (κ y).map (fun u => c y * u)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    have H := Kernel.measurable_kernel_prodMk_left (κ := κ)
      (((hc.comp measurable_fst).mul measurable_snd) hS)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext y
    exact Measure.map_apply (measurable_const.mul measurable_id) hS

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SmallCentralizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact balls in a root centralizer

The diagonal with weights 1, -1, and 0 contracts the centralizer of the
corresponding root in reverse time. In particular, it preserves each
closed matrix ball in that centralizer. These compact sets give measurable
sets of small returns in the proof of EKL (2006), Lemma 4.2.
-/

noncomputable section
open Filter Set Matrix MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Elementwise

namespace DukePrimeDegree
open PrimeDegreePackets

def rootContractionWeights {n : ℕ} (i j : Fin n) (r : Fin n) : ℝ :=
  (if r = i then 1 else 0) - (if r = j then 1 else 0)

lemma rootContractionWeights_sum {n : ℕ} (i j : Fin n) :
    ∑ r, rootContractionWeights i j r = 0 := by
  simp [rootContractionWeights, Finset.sum_sub_distrib]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralWeightSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite-dimensional neutral weight space

Real scalar closure of the trace-zero neutral weights supplies a
locally compact abelian group with Haar measure. Its diagonal action
is the same neutral action used in the exceptional-return argument.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def neutralWeightSpace {n : ℕ} (i j : Fin n) : Submodule ℝ (Fin n → ℝ) where
  carrier := {ell | (∑ r, ell r) = 0 ∧ ell i = ell j}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha, hai⟩ ⟨hb, hbi⟩
    constructor
    · simp only [Pi.add_apply, Finset.sum_add_distrib, ha, hb, add_zero]
    · simp only [Pi.add_apply, hai, hbi]
  smul_mem' := by
    rintro c a ⟨ha, hai⟩
    constructor
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ha, mul_zero]
    · simp only [Pi.smul_apply, hai]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_HorosphereIsolatingFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isolating a peripheral root of the shearing horosphere

Each noncentral row or column coordinate can be left unchanged by a
trace-zero diagonal flow which contracts all other horospherical
coordinates. The resulting conjugates converge to that single root.
-/

noncomputable section
open Matrix Filter
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def rowIsolatingRaw {n : ℕ} (i j k : Fin n) (r : Fin n) : ℝ :=
  if r = j then 1 else if r = i ∨ r = k then -1 else 0

def columnIsolatingRaw {n : ℕ} (i j k : Fin n) (r : Fin n) : ℝ :=
  if r = i then -1 else if r = j ∨ r = k then 1 else 0

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_EuclideanVelocityProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Measurable projections onto the actual component velocity spaces

The matrix topology has a concrete Euclidean model. Orthogonal projection
in that model gives a finite, measurably varying spanning family for the
actual stabilizer velocity space of every probability kernel. No choice
of subgroup curves or of a tangent basis is made measurably.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace

namespace DukePrimeDegree
open PrimeDegreePackets

abbrev MatrixEuclidean (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin n)

def matrixEuclideanLinearEquiv (n : ℕ) :
    MatrixEuclidean n ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun v i j := v (i, j)
  invFun V := WithLp.toLp 2 (fun p => V p.1 p.2)
  left_inv v := by ext p; rfl
  right_inv V := by ext i j; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def matrixEuclideanEquiv (n : ℕ) :
    MatrixEuclidean n ≃L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (matrixEuclideanLinearEquiv n).toContinuousLinearEquiv

@[simp]
lemma matrixEuclideanEquiv_apply (n : ℕ) (v : MatrixEuclidean n) (i j : Fin n) :
    matrixEuclideanEquiv n v i j = v (i, j) := rfl

@[simp]
lemma matrixEuclideanEquiv_symm_apply (n : ℕ)
    (V : Matrix (Fin n) (Fin n) ℝ) (p : Fin n × Fin n) :
    (matrixEuclideanEquiv n).symm V p = V p.1 p.2 := rfl

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ExactInvariantFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Pointwise invariant versions under a Haar measure class

The version is formed by averaging only on orbits where the observable
is almost everywhere constant. Those orbits form an exactly invariant
measurable set. This avoids an intersection of uncountably many conull
sets and does not assume amenability of the acting group.
-/

noncomputable section
open MeasureTheory Set Filter
open MeasureTheory.Measure
open scoped ENNReal

namespace DukePrimeDegree

variable {H Y : Type*} [Group H] [MeasurableSpace H]
  [MeasurableSpace Y] [MulAction H Y]

def orbitConstantMean (ρ : Measure H) (f : Y → ℝ) (x : Y) : ℝ :=
  ∫ h, f (h • x) ∂ρ

def orbitConstantSet (ρ : Measure H) (f : Y → ℝ) : Set Y :=
  {x | ∀ᵐ h ∂ρ, f (h • x) = orbitConstantMean ρ f x}

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ObservationConditionalProbability
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conditional probabilities of finite observations

The conditional entropy is the integral of the entropy of the actual
finite conditional distributions. Zero-mass conditioning cells contribute
zero, without requiring arbitrary probability distributions on them.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace PrimeDegreePackets

variable {Y α β : Type*} [MeasurableSpace Y] [Fintype α] [Fintype β]

def observationConditionalProbability (μ : Measure Y) (P : Y → α) (Q : Y → β)
    (a : α) (y : Y) : ℝ :=
  μ.real {z | (Q z,P z) = (Q y,a)} / μ.real {z | Q z = Q y}

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ObservationSigmaAlgebra
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sigma algebra and conditional expectations of finite observations -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace PrimeDegreePackets

variable {Y β : Type*} [mY : MeasurableSpace Y] [Fintype β]

@[instance_reducible] def observationSigma (Q : Y → β) : MeasurableSpace Y :=
  MeasurableSpace.comap Q ⊤

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_IntegrableCoboundary
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrable coboundaries have zero mean

Only the difference is assumed integrable. Truncating the transfer
function by one-Lipschitz clamps and applying dominated convergence
avoids any integrability assumption on the logarithmic normalization.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace DukePrimeDegree

def realClamp (M x : ℝ) : ℝ := max (-M) (min M x)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_MautnerLatticeL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mautner for the actual lattice L² action

Only the specified subgroup preserves the measure. Pullback by its
right action is a continuous isometric action on L². Thus a root-flow
invariant L² observable is also invariant under the opposite root and
the associated diagonal elements of that subgroup.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

def inverseDomainHom (H : Type*) [Group H] : H →* Hᵈᵐᵃ where
  toFun h := DomMulAct.mk h⁻¹
  map_one' := by simp
  map_mul' a b := by simp only [mul_inv_rev, DomMulAct.mk_mul]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_MaximalOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform control of visits to decreasing exceptional sets

The finite Hopf inequality bounds the probability of ever having an
excessive occupation average. Applied to decreasing null-intersection
sets, it gives almost-sure uniform control over every time interval.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

def excessiveOccupation {Y : Type*} (T : Y → Y) (A : Set Y) (δ : ℝ) : Set Y :=
  {x | ∃ n : ℕ, δ*n < (visitCount T A n x : ℝ)}

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PairedCoordinateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational operators scalar on two coordinates

The algebra below consists of concrete real matrices preserving the rational
row space and acting by a common scalar on two specified coordinate
functionals. In prime dimension, the generic-lattice condition forces this
algebra to contain only rational scalar matrices. No diagonal condition is
imposed on the other coordinates. This is the arithmetic form needed when
singleton root blocks are still present.
-/

noncomputable section
open Matrix Module Set
open scoped BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- A concrete matrix algebra, with the common coordinate eigenvalue recorded
as its first component. -/
def pairedCoordinateAlgebra {n : ℕ} (W : Submodule ℚ (Fin n → ℝ))
    (i j : Fin n) : Subalgebra ℚ (ℝ × Matrix (Fin n) (Fin n) ℝ) where
  carrier := {a | (∀ w ∈ W, a.2 *ᵥ w ∈ W) ∧
    (∀ v, (a.2 *ᵥ v) i = a.1 * v i) ∧
    (∀ v, (a.2 *ᵥ v) j = a.1 * v j)}
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro w _; simpa only [Prod.snd_zero, Matrix.zero_mulVec] using W.zero_mem
    · intro v; simp
    · intro v; simp
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro w hw; simpa using hw
    · intro v; simp
    · intro v; simp
  add_mem' := by
    rintro a b ⟨ha, hai, haj⟩ ⟨hb, hbi, hbj⟩
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      simpa only [Prod.fst_add, Prod.snd_add, Matrix.add_mulVec] using
        W.add_mem (ha w hw) (hb w hw)
    · intro v; simp only [Prod.snd_add, Prod.fst_add, Matrix.add_mulVec,
        Pi.add_apply, hai, hbi, add_mul]
    · intro v; simp only [Prod.snd_add, Prod.fst_add, Matrix.add_mulVec,
        Pi.add_apply, haj, hbj, add_mul]
  mul_mem' := by
    rintro a b ⟨ha, hai, haj⟩ ⟨hb, hbi, hbj⟩
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      simpa only [Prod.snd_mul, Matrix.mulVec_mulVec] using ha _ (hb w hw)
    · intro v
      simp only [Prod.snd_mul, Prod.fst_mul, ← Matrix.mulVec_mulVec, hai, hbi,
        mul_assoc]
    · intro v
      simp only [Prod.snd_mul, Prod.fst_mul, ← Matrix.mulVec_mulVec, haj, hbj,
        mul_assoc]
  algebraMap_mem' := by
    intro q
    change (∀ w ∈ W, (algebraMap ℚ (Matrix (Fin n) (Fin n) ℝ) q) *ᵥ w ∈ W) ∧
      (∀ v, ((algebraMap ℚ (Matrix (Fin n) (Fin n) ℝ) q) *ᵥ v) i =
        (q : ℝ) * v i) ∧
      (∀ v, ((algebraMap ℚ (Matrix (Fin n) (Fin n) ℝ) q) *ᵥ v) j =
        (q : ℝ) * v j)
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      simpa only [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
        Matrix.one_mulVec] using W.smul_mem q hw
    · intro v
      simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Rat.smul_def]
    · intro v
      simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Rat.smul_def]

def pairedCoordinateEval {n : ℕ} (W : Submodule ℚ (Fin n → ℝ))
    (i j : Fin n) : pairedCoordinateAlgebra W i j →ₐ[ℚ] ℝ where
  toFun a := a.val.1
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

instance pairedCoordinateModule {n : ℕ} (W : Submodule ℚ (Fin n → ℝ))
    (i j : Fin n) : Module (pairedCoordinateAlgebra W i j) W where
  smul a w := ⟨a.val.2 *ᵥ w.val, a.property.1 w.val w.property⟩
  one_smul w := by
    apply Subtype.ext
    exact Matrix.one_mulVec _
  mul_smul a b w := by
    apply Subtype.ext
    change (a.val.2 * b.val.2) *ᵥ w.val = a.val.2 *ᵥ (b.val.2 *ᵥ w.val)
    exact (Matrix.mulVec_mulVec _ _ _).symm
  smul_zero a := by
    apply Subtype.ext
    change a.val.2 *ᵥ 0 = 0
    exact Matrix.mulVec_zero _
  smul_add a v w := by
    apply Subtype.ext
    change a.val.2 *ᵥ (v.val + w.val) = a.val.2 *ᵥ v.val + a.val.2 *ᵥ w.val
    exact Matrix.mulVec_add _ _ _
  add_smul a b w := by
    apply Subtype.ext
    change (a.val.2 + b.val.2) *ᵥ w.val = a.val.2 *ᵥ w.val + b.val.2 *ᵥ w.val
    exact Matrix.add_mulVec _ _ _
  zero_smul w := by
    apply Subtype.ext
    change (0 : Matrix (Fin n) (Fin n) ℝ) *ᵥ w.val = 0
    exact Matrix.zero_mulVec _

instance pairedCoordinateTower {n : ℕ} (W : Submodule ℚ (Fin n → ℝ))
    (i j : Fin n) : IsScalarTower ℚ (pairedCoordinateAlgebra W i j) W where
  smul_assoc q a w := by
    apply Subtype.ext
    exact Matrix.smul_mulVec q a.val.2 w.val

def pairedCoordinateActionAt {n : ℕ} (W : Submodule ℚ (Fin n → ℝ))
    (i j : Fin n) (w : W) : pairedCoordinateAlgebra W i j →ₗ[ℚ] W where
  toFun a := a • w
  map_add' a b := add_smul a b w
  map_smul' q a := smul_assoc q a w

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ScalarOrbitCommutant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar real commutants of prime-degree finite root-pair orbits

Rationality of the actual lattice stabilizer's commutant turns the preceding
rational scalar theorem into a real scalar theorem. In particular, no
nontrivial real projection can commute with the orbit group. No orbit
existence is assumed beyond the finite invariant orbit explicitly supplied.
-/

noncomputable section
open Matrix Set MeasureTheory
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def scalarMatrixSpace (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  (Algebra.linearMap ℝ (Matrix (Fin n) (Fin n) ℝ)).range

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SeparatedOrbitCover
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable separated covers for the diagonal-map section construction -/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree

section Topology
variable {Y : Type*} [TopologicalSpace Y]

def finiteOrbitNeighbor (e : Y ≃ₜ Y) (N : ℕ) (x y : Y) : Prop :=
  x=y ∨ ∃ k : Fin N, (e^(k.val+1)) x=y ∨ (e^(k.val+1)) y=x

/-- The orbit relation is used only to say that the section meets each
orbit. Its finite-neighbor relation controls the measure of the section. -/
def homeomorphOrbitSetoid (e : Y ≃ₜ Y) : Setoid Y where
  r x y := ∃ k : ℤ, (e^k) x=y
  iseqv := {
    refl := fun x => ⟨0,by simp⟩
    symm := by
      rintro x y ⟨k,rfl⟩
      refine ⟨-k,?_⟩
      rw [←Homeomorph.mul_apply,←zpow_add]
      simp
    trans := by
      rintro x y z ⟨k,rfl⟩ ⟨l,rfl⟩
      refine ⟨l+k,?_⟩
      rw [zpow_add,Homeomorph.mul_apply] }

end Topology

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transverse representatives using only a single root block

On an ergodic component for a single root block, an arbitrary ambient
diagonal correction need not preserve the component measure.  Here the
correction is a product of roots in that block.  It clears the entries
inside the block and equalizes its diagonal, leaving the complementary
coordinates unrestricted.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def singleBlockSetoid {n : ℕ} (S : Set (Fin n)) : Setoid (Fin n) where
  r i j := i = j ∨ (i ∈ S ∧ j ∈ S)
  iseqv := ⟨fun _ => Or.inl rfl, by aesop, by aesop⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockTransverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A single-block correction retains a transverse limiting shear

Only the selected block is normalized to a scalar. Its complement may
have arbitrary entries. Conjugation by the selected root group fixes
the entire block-diagonal part, so every nonidentity limiting shear is
outside the two-block preserving group.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def blockComplementSetoid {n : ℕ} (S : Set (Fin n)) : Setoid (Fin n) where
  r i j := i ∈ S ↔ j ∈ S
  iseqv := ⟨fun _ => Iff.rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_TranslationInvariantSlices
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.xMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Haar slices of a measure invariant in its second coordinate

Only relatively compact transverse sets are needed for local product charts.
The transverse measure itself is allowed to be singular.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DukePrimeDegree

variable {Z V : Type*} [MeasurableSpace Z] [MeasurableSpace V]

def secondCoordinateSlice (ρ : Measure (Z × V)) (A : Set Z) : Measure V :=
  (ρ.restrict (A ×ˢ univ)).map Prod.snd

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_TranslationInvariantProduct
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.xMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting off a translation-invariant neutral factor -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DukePrimeDegree

variable {Z V : Type*} [MeasurableSpace Z] [MeasurableSpace V]

def firstCoordinateSlice (ρ : Measure (Z × V)) (K : Set V) : Measure Z :=
  (ρ.restrict (univ ×ˢ K)).map Prod.fst

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_WeylReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Permuting coordinates on the arithmetic quotient

Coordinate reversal transfers the increasing regular weight construction
to its decreasing counterpart. Reindexing preserves determinant one and
the integral lattice, so it acts on the actual quotient.
-/

noncomputable section
open Matrix MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

def reindexSpecialLinear {n : ℕ} (R : Type*) [CommRing R]
    (e : Equiv.Perm (Fin n)) :
    Matrix.SpecialLinearGroup (Fin n) R ≃* Matrix.SpecialLinearGroup (Fin n) R where
  toFun M := ⟨Matrix.reindex e e M.val, by rw [Matrix.det_reindex_self]; exact M.prop⟩
  invFun M := ⟨Matrix.reindex e.symm e.symm M.val,
    by rw [Matrix.det_reindex_self]; exact M.prop⟩
  left_inv M := by
    apply Subtype.ext
    ext i j
    change M.val (e.symm (e i)) (e.symm (e j)) = M.val i j
    rw [e.symm_apply_apply, e.symm_apply_apply]
  right_inv M := by
    apply Subtype.ext
    ext i j
    change M.val (e (e.symm i)) (e (e.symm j)) = M.val i j
    rw [e.apply_symm_apply, e.apply_symm_apply]
  map_mul' A B := by
    apply Subtype.ext
    exact (Matrix.reindexRingEquiv R e).map_mul A.val B.val

lemma continuous_reindexSpecialLinear {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Continuous (reindexSpecialLinear ℝ e) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply (e.symm j)).comp
      ((continuous_apply (e.symm i)).comp continuous_subtype_val)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_WeylEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy under coordinate permutations of the quotient -/

noncomputable section
open MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

lemma permutedWeight_sum {n : ℕ} (e : Equiv.Perm (Fin n))
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) :
    ∑ i, ell (e.symm i) = 0 := by
  rw [Equiv.sum_comp]
  exact hell

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_WeylAtomicRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate permutations transport atomic intrinsic root leaves -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma reindex_transvection {n : ℕ} (e : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : i ≠ j) (t : ℝ) :
    reindexSpecialLinear ℝ e (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection (e.injective.ne hij) t := by
  apply Subtype.ext
  ext a b
  change ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.single i j t) (e.symm a) (e.symm b) =
    ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.single (e i) (e j) t) a b
  simp only [Matrix.add_apply,Matrix.one_apply,Matrix.single_apply,
    e.symm.injective.eq_iff,e.eq_symm_apply]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RareLabelEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entropy cost of rare observation errors

This finite-label estimate converts small boundary-visit frequencies
into a small entropy cost for the neutral orbit covers.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def rareLabelCost (q : ℕ) (δ ε : ℝ) : ℝ :=
  -Real.log (1-δ) + ε * (Real.log q - Real.log δ)

def observationError {Y α : Type*} [DecidableEq α] (P R : Y → α) (y : Y) : Option α :=
  if P y = R y then none else some (P y)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_SummablePartitionBoundaries
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing partition cuts with summable boundary returns

Almost every real cut of a measurable real-valued function has summable
strip masses for any summable sequence of widths. Invariant dynamics
therefore avoid those shrinking strips eventually almost everywhere.
This supplies the boundary control for partitions subordinate to
contracting root leaves.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace DukePrimeDegree

variable {Y : Type*} [MeasurableSpace Y]

def realBoundaryStrip (f : Y → ℝ) (r ε : ℝ) : Set Y :=
  {x | |f x-r| ≤ ε}

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_DyadicBoundaryCuts
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Distance cuts with uniform quantitative boundary bounds

One cut controls all dyadic widths. The constant depends only on the
length of the interval from which the cut is selected, not the observable
or the probability measure.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace DukePrimeDegree

variable {Y : Type*} [MeasurableSpace Y]

def dyadicBoundaryCost (μ : Measure Y) (f : Y → ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal ((2:ℝ)^k) * μ (realBoundaryStrip f r ((1/4:ℝ)^k))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_LayeredObservations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Encoding finite observations chosen by an integer height -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace DukePrimeDegree

def layeredObservation {Y : Type*} {N : ℕ → ℕ} (H : Y → ℕ)
    (P : ∀ m, Y → Fin (N m)) (x : Y) : ℕ := Nat.pair (H x) (P (H x) x).val

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CutFamilyCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite integer codes for families of real cuts -/

noncomputable section
open MeasureTheory
namespace DukePrimeDegree

def finiteCutCode {Y : Type*} {N : ℕ} (f : Fin N → Y → ℝ) (c : Fin N → ℝ)
    (x : Y) : Fin (Fintype.card (Fin N → Bool)) :=
  Fintype.equivFin (Fin N → Bool) (fun i => decide (f i x < c i))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuantitativeDistanceNet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative distance nets on logarithmic quotient balls

Finite matrix grids give nets for the intrinsic quotient distance. In
the other direction a small quotient distance gives a small actual
right lift, which is what the future-fiber construction needs.
-/

noncomputable section
open Set
open scoped Topology Matrix.Norms.Operator
namespace DukePrimeDegree
open PrimeDegreePackets

def quotientNetBound (n : ℕ) (R s : ℝ) : ℝ :=
  (2*Real.exp (R+1)+2)^(n*n) /
    (min 1 ((s/(12*(n:ℝ)))/(4*(n:ℝ)*Real.exp (R+1))))^(n*n)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditioningFiniteLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditioning a leaf kernel on a finite observed label

Adding a finite label to the transverse coordinate restricts the actual
conditional leaf to the corresponding label fiber and normalizes it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [StandardBorelSpace T] [Nonempty T]

def finiteLabelLift {N : ℕ} (Q : S × T → Fin N) (z : S × T) : (S × Fin N) × T :=
  ((z.1,Q z),z.2)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_HeightObservationEntropy
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.xMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy controlled by the increments of a height

A finite label reconstructed from its next value and a finite increment
code has entropy rate bounded by the entropy of that code. In particular,
all finite truncations of a height changing by at most one have entropy
rate at most `log 3`, regardless of the height's integrability.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

variable {Y : Type*} [MeasurableSpace Y]

def heightClip (H : Y → ℕ) (N : ℕ) (y : Y) : Fin (N+1) :=
  ⟨min (H y) N,Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma heightClip_measurable {H : Y → ℕ} (hH : Measurable H) (N : ℕ) :
    Measurable (heightClip H N) :=
  (measurable_of_countable (fun k : ℕ =>
    (⟨min k N,Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (N+1)))).comp hH

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RareTernaryEntropy
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy of a rare three-valued increment

When a three-valued increment is usually the middle value, its entropy
is bounded by binary entropy plus the exceptional mass times `log 2`.
The bound tends to zero with the exceptional mass.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

def rareTernaryCost (p : ℝ) : ℝ :=
  Real.negMulLog p + Real.negMulLog (1-p) + p*Real.log 2

@[simp] lemma rareTernaryCost_zero : rareTernaryCost 0=0 := by
  simp [rareTernaryCost]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_HeightBoundaryCount
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the boundaries of shifted height bins

A natural height crosses exactly one of the `q` shifted bin boundaries
when incremented by one. Integrating this identity controls boundary
frequencies without requiring the height itself to be integrable.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree

variable {Y : Type*} [MeasurableSpace Y]

def heightBoundary (H : Y → ℕ) (q r : ℕ) : Set Y :=
  {x | (H x+r+1)/q ≠ (H x+r)/q}

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_BilateralFiniteCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite codes exhausting the actual bilateral itinerary factor -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

def truncateBilateralCode {m l : ℕ} (hml : m ≤ l)
    (v : (Fin l → Fin (l+1)) × (Fin l → Fin (l+1))) :
    (Fin m → Fin (m+1)) × (Fin m → Fin (m+1)) :=
  (fun i => ⟨min (v.1 ⟨i.val,lt_of_lt_of_le i.isLt hml⟩).val m,
      Nat.lt_succ_of_le (min_le_right _ _)⟩,
   fun i => ⟨min (v.2 ⟨i.val,lt_of_lt_of_le i.isLt hml⟩).val m,
      Nat.lt_succ_of_le (min_le_right _ _)⟩)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ObservationInformation
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrable pointwise information of finite observations -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

def observationInformation {Y α : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (P : Y → α) (y : Y) : ℝ :=
  -Real.log (ν.real {z | P z=P y})

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalInformation
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional entropy as the mean pointwise information

The finite observed variable has a regular conditional distribution even
when the conditioning sigma algebra is arbitrary. Lifting its underlying
space keeps the ambient and conditioning measurable structures distinct.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

def conditionalInformation {Y α : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (P : Y → α) (m : MeasurableSpace Y) (y : Y) : ℝ :=
  -Real.log ((μ[({z | P z=P y}.indicator (fun _ => (1:ℝ))) | m]) y)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_CountableFutureCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite codes converging to the future of a countable observation

Both the time interval and the clipping level increase. The limiting atom
records every future value of the original countable observation.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets

def countableFutureCode {Y : Type*} (T : Y → Y) (Q : Y → ℕ) (m : ℕ)
    (y : Y) : Fin (Fintype.card (Fin m → Fin (m+1))) :=
  Fintype.equivFin _ (fun i : Fin m => heightClip Q m (T^[i.val+1] y))

lemma countableFutureCode_measurable {Y : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q) (m : ℕ) :
    Measurable (countableFutureCode T Q m) :=
  (measurable_of_finite (Fintype.equivFin (Fin m → Fin (m+1)))).comp
    (measurable_pi_iff.mpr fun i => (heightClip_measurable hQ m).comp (hT.iterate (i.val+1)))

def truncateCountableFutureCode {m n : ℕ} (hmn : m ≤ n)
    (v : Fin (Fintype.card (Fin n → Fin (n+1)))) :
    Fin (Fintype.card (Fin m → Fin (m+1))) :=
  Fintype.equivFin _ (fun i : Fin m =>
    ⟨min ((Fintype.equivFin (Fin n → Fin (n+1))).symm v
      ⟨i.val,lt_of_lt_of_le i.isLt hmn⟩).val m,
      Nat.lt_succ_of_le (min_le_right _ _)⟩)

def countableFutureFiber {S V Y : Type*} (T : Y → Y) (Q : Y → ℕ)
    (F : S × V → Y) (z : S × V) : Set V :=
  {t | ∀ k : ℕ, Q (T^[k+1] (F (z.1,t)))=Q (T^[k+1] (F z))}

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FutureSigmaAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact transverse and future conditioning sigma algebra -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma observationSigma_comp_eq_comap {Y Z α : Type*} (F : Z → Y) (P : Y → α) :
    observationSigma (P ∘ F) = MeasurableSpace.comap F (observationSigma P) := by
  rw [observationSigma,observationSigma,MeasurableSpace.comap_comp]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_CountableFutureSigma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact sigma algebra of the countable future codes -/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets

theorem countableFutureCode_sigma_generate {Y : Type*}
    (T : Y → Y) (Q : Y → ℕ) :
    (⨆ m, observationSigma (countableFutureCode T Q m)) =
      ⨆ k : ℕ, observationSigma (fun y => Q (T^[k+1] y)) := by
  apply le_antisymm
  · let : MeasurableSpace Y := ⨆ k : ℕ, observationSigma (fun y => Q (T^[k+1] y))
    apply iSup_le
    intro m
    have hQ (k : ℕ) : Measurable (fun y => Q (T^[k+1] y)) :=
      (comap_measurable (fun y => Q (T^[k+1] y))).iSup' k
    have hc : Measurable (countableFutureCode T Q m) := by
      apply (measurable_of_finite (Fintype.equivFin (Fin m → Fin (m+1)))).comp
      exact measurable_pi_iff.mpr fun i =>
        (heightClip_measurable (measurable_id : Measurable (id : ℕ → ℕ)) m).comp (hQ i.val)
    exact hc.comap_le
  · let : MeasurableSpace Y := ⨆ m, observationSigma (countableFutureCode T Q m)
    apply iSup_le
    intro k
    have hQ : Measurable (fun y => Q (T^[k+1] y)) := by
      apply measurable_to_countable'
      intro a
      let m := max (k+1) (a+1)
      have hk : k < m := by dsimp only [m]; omega
      have ha : a < m := by dsimp only [m]; omega
      let f : Fin (Fintype.card (Fin m → Fin (m+1))) → ℕ :=
        fun v => ((Fintype.equivFin (Fin m → Fin (m+1))).symm v ⟨k,hk⟩).val
      have hc : Measurable (countableFutureCode T Q m) :=
        (comap_measurable (countableFutureCode T Q m)).iSup' m
      have he : {y | Q (T^[k+1] y)=a} = {y | f (countableFutureCode T Q m y)=a} := by
        ext y
        simp only [f,countableFutureCode,Equiv.symm_apply_apply]
        change Q (T^[k+1] y)=a ↔ min (Q (T^[k+1] y)) m=a
        omega
      change MeasurableSet {y | Q (T^[k+1] y)=a}
      rw [he]
      exact measurableSet_eq_fun ((measurable_of_finite f).comp hc) measurable_const
    exact hQ.comap_le

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_CountableFutureMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire future as a measurable sequence

This representation makes future-measurable events constant on each
complete future fiber. It is used to restrict local disintegrations to
saturated events when gluing them.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

def entireFutureObservation {Y : Type*} (T : Y → Y) (Q : Y → ℕ)
    (y : Y) : ℕ → ℕ := fun k => Q (T^[k+1] y)

lemma entireFutureObservation_measurable {Y : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q) :
    Measurable (entireFutureObservation T Q) :=
  measurable_pi_iff.mpr fun k => hQ.comp (hT.iterate (k+1))

lemma countableFutureSigma_eq_comap {Y : Type*} (T : Y → Y) (Q : Y → ℕ) :
    (⨆ k : ℕ, observationSigma (fun y => Q (T^[k+1] y))) =
      MeasurableSpace.comap (entireFutureObservation T Q)
        (inferInstance : MeasurableSpace (ℕ → ℕ)) := by
  exact (MeasurableSpace.comap_process_pi
    (fun k : ℕ => fun y : Y => Q (T^[k+1] y))).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_LayeredPredecessors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the three possible predecessor height levels -/

noncomputable section
open Set
namespace DukePrimeDegree

def UniformFinitePredecessors {Y : Type*} (T : Y → Y) (Q : Y → ℕ) : Prop :=
  ∃ M : ℕ, ∀ q : ℕ, ∃ F : Finset ℕ, Q '' {y | Q (T y)=q} ⊆ F ∧ F.card ≤ M

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FutureLabelBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite blocks of countable future labels -/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets

def futureLabelBlock {Y : Type*} (T : Y → Y) (Q : Y → ℕ) (N : ℕ) (x : Y) : ℕ :=
  Encodable.encode (fun i : Fin N => Q (T^[i.val+1] x))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_LastActiveObservation
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable observations at the last active scale

Summably small sections overlap only finitely often almost everywhere.
Recording the largest active scale therefore preserves arbitrarily fine
visits while keeping the observation alphabet countable.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree

def lastActiveSection {Y : Type*} (S : ℕ → Set Y) (n : ℕ) : Set Y :=
  {x | x ∈ S n ∧ ∀ m, n < m → x ∉ S m}

def lastActiveObservationAtom {Y : Type*} (S : ℕ → Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) : Option (Σ n : ℕ, Fin (K n)) → Set Y
  | none => (⋃ n, lastActiveSection S n)ᶜ
  | some z => {x | x ∈ lastActiveSection S z.1 ∧ B z.1 x=z.2}

lemma lastActiveObservation_covers {Y : Type*} (S : ℕ → Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) (x : Y) :
    ∃ z, x ∈ lastActiveObservationAtom S B z := by
  classical
  by_cases h : ∃ n, x ∈ lastActiveSection S n
  · obtain ⟨n,hn⟩ := h
    exact ⟨some ⟨n,B n x⟩,hn,rfl⟩
  · exact ⟨none,by simpa only [lastActiveObservationAtom,mem_compl_iff,mem_iUnion,not_exists] using h⟩

def lastActiveObservation {Y : Type*} (S : ℕ → Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) (x : Y) :
    Option (Σ n : ℕ, Fin (K n)) := (lastActiveObservation_covers S B x).choose

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_PeriodicEntropyZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Almost-everywhere periodicity gives zero finite-observation entropy

A common positive period makes every long orbit name a deterministic
extension of one fixed finite name.  Thus block entropy stays bounded and
its entropy rate is zero.  Combining this with full-A ergodicity isolates
the aperiodic branch without asserting ergodicity of the chosen map.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

def periodicNameExtension (α : Type*) (n : ℕ) (hn : 0 < n) (N : ℕ)
    (w : Fin n → α) : Fin N → α :=
  fun j => w ⟨j.val % n, Nat.mod_lt _ hn⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_PredecessorWholeFutureSigma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One predecessor restores exactly one level of the whole future -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

abbrev fullFutureSigma {Y : Type*} (T : Y → Y) (Q : Y → ℕ) (r : ℕ) :
    MeasurableSpace Y :=
  ⨆ k : ℕ, observationSigma (fun x => Q (T^[r+k] x))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_DiracFiberGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common full-measure graph for Dirac fiber conditionals -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree

variable {Z U : Type*} [MeasurableSpace Z] [MeasurableSpace U]
  [StandardBorelSpace U]

def kernelDiracGraph (κ : Kernel Z U) : Set (Z × U) :=
  {z | κ z.1=Measure.dirac z.2}

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FiniteProjectionFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite frame selection by Gram determinants

The projected coordinate vectors form a finite measurable spanning family.
Maximal nonzero Gram minors select a basis from that family. All tests used
in the selection are measurable real determinants, so this does not assume
a measurable tangent-frame theorem.
-/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators InnerProductSpace

namespace DukePrimeDegree

section GramFrames

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def frameEnumeration (I : Type*) [Fintype I] [DecidableEq I]
    (k : ℕ) : Finset I :=
  if hk : k < Fintype.card (Finset I) then
    (Fintype.equivFin (Finset I)).symm ⟨k, hk⟩ else ∅

theorem frameEnumeration_surjective (S : Finset I) :
    ∃ k, frameEnumeration I k = S := by
  let k := Fintype.equivFin (Finset I) S
  refine ⟨k.val, ?_⟩
  simp only [frameEnumeration, k.isLt, dite_true]
  exact (Fintype.equivFin (Finset I)).symm_apply_apply S

def finiteFrameVector (v : I → E) (S : Finset I) (j : ℕ) : E :=
  if hj : j < S.card then v ((S.equivFin.symm ⟨j, hj⟩).val) else 0

end GramFrames

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FirstCoverCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One covering label instead of the full vector of cut tests

A point is labeled by one cut containing it. There are N+1 labels for N
cuts. Equality of labels still puts covered points in the same small
set, while constancy of all cut tests implies constancy of this label.
-/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree

def firstTrue {N : ℕ} (w : Fin N → Bool) : Fin (N+1) :=
  if h : ∃ i, w i=true then ⟨h.choose.val+1,Nat.succ_lt_succ h.choose.isLt⟩ else 0

def firstCoverCode {Y : Type*} {N : ℕ} (f : Fin N → Y → ℝ)
    (c : Fin N → ℝ) (x : Y) : Fin (N+1) :=
  firstTrue (fun i => decide (f i x < c i))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PluckerCovariance
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual frame minors under diagonal transport

The projective coordinates here are determinants of minors of an actual
real matrix frame. Changing its basis multiplies every coordinate by the
same determinant. Thus diagonal recurrence applies to these coordinates
without an assumed projective-action interface.
-/

noncomputable section
open MeasureTheory Filter Set Matrix
open scoped BigOperators ENNReal

namespace DukePrimeDegree

def frameMinor {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ)
    (p : Fin k ↪ Fin n) : ℝ := (B.submatrix p id).det

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FrameWeightRigidity
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From minor weights to an invariant subspace

In a genuine Grassmannian coordinate chart, the pivot rows of a frame
form the identity. A one-row replacement minor is then exactly the
corresponding graph coordinate. The single-weight minor conclusion
therefore forces the frame to intertwine the two diagonal operators.
-/

noncomputable section
open MeasureTheory Filter Matrix Set
open scoped BigOperators

namespace DukePrimeDegree

def replaceFramePivot {n k : ℕ} (p : Fin k ↪ Fin n) (j : Fin k) (i : Fin n) :
    Fin k ↪ Fin n := p.trans (Equiv.swap (p j) i).toEmbedding

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_GoodSetFiberCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Correcting a pair inside a large generic set

The two initial points may be corrected by a changing element of the
measure stabilizer.  Averaging the bad set along a fixed group patch
gives a larger good set.  For two points in that larger set, a common
group translation restores membership in the original generic set.
No commutation with the averaging flow is needed for this selection.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace DukePrimeDegree

section FiberMass

variable {H Y : Type*} [MeasurableSpace H] [MeasurableSpace Y]

def badOrbitFiberMass (ρ : Measure H) (R : Y → H → Y)
    (K : Set H) (G : Set Y) (x : Y) : ℝ≥0∞ :=
  ∫⁻ h in K, Gᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (R x h) ∂ρ

end FiberMass

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LocalQuotientPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform local packing after rescaling a quotient chart

The number of separated points in a fixed multiple of a sufficiently
small chart is bounded independently of the chart radius and base point.
The proof uses the existing finite matrix grid and actual right lifts.
-/

noncomputable section
open Matrix Set
open scoped Topology Matrix.Norms.Operator
namespace DukePrimeDegree
open PrimeDegreePackets

def localQuotientPackingBound (n : ℕ) (C : ℝ) : ℝ :=
  (2*C+2)^(n*n)/(1/(96*(n:ℝ)^2))^(n*n)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_MatrixCoordinateFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coordinate frames on the actual velocity-rank events

The finite-dimensional recurrence argument uses rectangular matrices with
one natural-number row dimension. Flattening the actual matrix space is
only a linear change of coordinates. On each measurable rank event the
selected velocity frame has independent columns and spans the actual
velocity space; outside that event the rectangular frame is zero.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def matrixCoordinateEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ ≃ₗ[ℝ] (Fin (n * n) → ℝ) where
  toFun V q := V (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2
  invFun v i j := v (finProdFinEquiv (i, j))
  left_inv V := by
    ext i j
    change V (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = V i j
    rw [Equiv.symm_apply_apply]
  right_inv v := by
    ext q
    change v (finProdFinEquiv (finProdFinEquiv.symm q)) = v q
    rw [Equiv.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def matrixCoordinateWeight {n : ℕ} (ell : Fin n → ℝ) (q : Fin (n * n)) : ℝ :=
  Real.exp (ell (finProdFinEquiv.symm q).1 - ell (finProdFinEquiv.symm q).2)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralTransverseCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual neutral coordinate in the upper-root chart

On the positive-diagonal chart the transverse slice is the product of its
unit-diagonal part and the trace-zero logarithmic diagonal. Right diagonal
translation fixes the first coordinate and translates the second. This is
the local center coordinate needed for comparison with the root kernel.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

abbrev transverseNeutralSpace (n : ℕ) : Submodule ℝ (Fin n → ℝ) where
  carrier := {v | ∑ i, v i=0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change ∑ i, v i=0 at hv
    change ∑ i, w i=0 at hw
    change ∑ i, (v+w) i=0
    simp only [Pi.add_apply,Finset.sum_add_distrib,hv,hw,add_zero]
  smul_mem' := by
    intro c v hv
    change ∑ i, v i=0 at hv
    change ∑ i, (c • v) i=0
    simp only [Pi.smul_apply,smul_eq_mul,←Finset.mul_sum,hv,mul_zero]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NormalizedFrame
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Diagonal invariance of an actual frame

A nonzero pivot minor gives a concrete normalized frame, by multiplying
on the right by that minor's inverse.  The one-weight conclusion for
the original minors then makes its column space diagonal-invariant.
The pivot may be chosen separately at each point; no invariant chart
or measurable choice of the pivot is assumed.
-/

noncomputable section
open MeasureTheory Filter Matrix Set
open scoped BigOperators

namespace DukePrimeDegree

def normalizeFrame {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ)
    (p : Fin k ↪ Fin n) : Matrix (Fin n) (Fin k) ℝ :=
  B * (B.submatrix p id)⁻¹

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_OpenRegionEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An injective coordinate image for a local homeomorphism -/

open Set
namespace DukePrimeDegree

lemma openEmbedding_on_coordinate_image {A B X : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
    (e : A → B) (f : B → X) (V : Set A)
    (he : Topology.IsOpenEmbedding e) (hf : IsLocalHomeomorph f) (hV : IsOpen V)
    (hcomp : Topology.IsOpenEmbedding (V.domRestrict (f ∘ e))) :
    Topology.IsOpenEmbedding ((e '' V).domRestrict f) := by
  have hU : IsOpen (e '' V) := he.isOpenMap V hV
  apply Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  refine ⟨hf.continuous.comp continuous_subtype_val,?_,hf.isOpenMap.comp hU.isOpenEmbedding_subtypeVal.isOpenMap⟩
  intro x y hxy
  obtain ⟨v,hv,hvx⟩ := x.prop
  obtain ⟨w,hw,hwy⟩ := y.prop
  have hvw : (⟨v,hv⟩ : V) = ⟨w,hw⟩ := hcomp.injective (by
    change f (e v) = f (e w)
    rw [hvx,hwy]
    exact hxy)
  exact Subtype.ext (hvx.symm.trans ((congrArg e (congrArg Subtype.val hvw)).trans hwy))

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootFactorTransversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering the transverse embedding in an affine root chart -/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma isOpenEmbedding_of_prodMap_real {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {e : A → B} (h : Topology.IsOpenEmbedding (Prod.map e (id : ℝ → ℝ))) :
    Topology.IsOpenEmbedding e := by
  have he : Topology.IsEmbedding e :=
    (isEmbedding_prodMkLeft (0 : ℝ)).of_comp_iff.mp
      (h.isEmbedding.comp (isEmbedding_prodMkLeft (0 : ℝ)))
  apply Topology.IsOpenEmbedding.of_isEmbedding_isOpenMap he
  intro U hU
  have H := isOpenMap_fst _ (h.isOpenMap _ (hU.prod isOpen_univ))
  have hs : Prod.fst '' (Prod.map e (id : ℝ → ℝ) '' (U ×ˢ univ)) = e '' U := by
    ext b
    constructor
    · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
      exact ⟨z.1,hz.1,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨(e a,0),⟨(a,0),⟨ha,mem_univ _⟩,rfl⟩,rfl⟩
  rwa [hs] at H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ShiftedRootPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual coordinate measures for root charts with varying time origins -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]

def realFiberShift {S : Type*} [MeasurableSpace S] (τ : S → ℝ) (hτ : Measurable τ) :
    (S × ℝ) ≃ᵐ (S × ℝ) where
  toFun z := (z.1,z.2 + τ z.1)
  invFun z := (z.1,z.2 - τ z.1)
  left_inv z := by dsimp; congr 1; ring
  right_inv z := by dsimp; congr 1; ring
  measurable_toFun := measurable_fst.prodMk (measurable_snd.add (hτ.comp measurable_fst))
  measurable_invFun := measurable_fst.prodMk (measurable_snd.sub (hτ.comp measurable_fst))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootTransverseRectangles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product neighborhoods for the remaining-root transversals -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

structure RootTransverseRectangle {T B : Type*} [TopologicalSpace T] [TopologicalSpace B]
    (D : Set (T × B)) where
  first : Set T
  second : Set B
  first_open : IsOpen first
  second_open : IsOpen second
  inside : first ×ˢ second ⊆ D

namespace RootTransverseRectangle
variable {T B : Type*} [TopologicalSpace T] [TopologicalSpace B] {D : Set (T × B)}

def inclusion (C : RootTransverseRectangle D) (z : C.first × C.second) : D :=
  ⟨(z.1.val,z.2.val),C.inside ⟨z.1.prop,z.2.prop⟩⟩

lemma inclusion_isOpenEmbedding (C : RootTransverseRectangle D) (hD : IsOpen D) :
    Topology.IsOpenEmbedding C.inclusion := by
  have H := C.first_open.isOpenEmbedding_subtypeVal.prodMap
    C.second_open.isOpenEmbedding_subtypeVal
  exact Topology.IsOpenEmbedding.of_comp C.inclusion hD.isOpenEmbedding_subtypeVal H

end RootTransverseRectangle

end DukePrimeDegree

end

end OAI
end


