-- Prove2me | Definitions.Def_OAIQ244Duke023
-- name    : OAIQ244Duke023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:18:04.305167+00:00
-- url     : https://prove2.me/theorems/a92eaae5-50fb-4b7d-8814-8213a61c32f8
-- title:
--   Definitions bundle OAIQ244Duke023 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 291 declarations of OpenAI's Lean: 138 definitions, 1 inductive type or structure, 20 instances and 132 theorems. The definitions and types are `OAI.DukePrimeDegree.RootHorosphereShape`, `OAI.DukePrimeDegree.basisProbabilityTests`, `OAI.DukePrimeDegree.bilateralFiniteCode`, `OAI.DukePrimeDegree.bilateralNameFiber`, `OAI.DukePrimeDegree.bilateralNameObservation`, `OAI.DukePrimeDegree.blockRootGroup`, `OAI.DukePrimeDegree.canonicalRealEmbeddings`, `OAI.DukePrimeDegree.compactReturnSet`, `OAI.DukePrimeDegree.complementaryMatrix`, `OAI.DukePrimeDegree.fixedFieldMultiplicity`, `OAI.DukePrimeDegree.futureFiberCoordinateKernel`, `OAI.DukePrimeDegree.futureFiberTimeKernel`, `OAI.DukePrimeDegree.futureSliceKernel`, `OAI.DukePrimeDegree.instMeasurableSpaceG`, `OAI.DukePrimeDegree.latticeOrbitStabilizer`, `OAI.DukePrimeDegree.latticeStabilizerMatrix`, `OAI.DukePrimeDegree.matrixClosedBall`, `OAI.DukePrimeDegree.matrixVelocitySpace`, `OAI.DukePrimeDegree.neutralSpaceDiagonal`, `OAI.DukePrimeDegree.normalizedFutureSliceKernel`, `OAI.DukePrimeDegree.normalizedRescaledRealKernel`, `OAI.DukePrimeDegree.quotientLiftMeasure`, `OAI.DukePrimeDegree.quotientLogDistance`, `OAI.DukePrimeDegree.quotientReindex`, `OAI.DukePrimeDegree.quotientReindexHomeomorph`, `OAI.DukePrimeDegree.rationalRowSpace`, `OAI.DukePrimeDegree.reindexLogCoordinates`, `OAI.DukePrimeDegree.rightDisplacementLengths`, `OAI.DukePrimeDegree.rootHitTimes`, `OAI.DukePrimeDegree.rootPairConjugate`, `OAI.DukePrimeDegree.rootPairFlow`, `OAI.DukePrimeDegree.rootRationalBad`, `OAI.DukePrimeDegree.rootReindexCoordinates`, `OAI.DukePrimeDegree.rootShearSize`, `OAI.DukePrimeDegree.rootShearingKappa`, `OAI.DukePrimeDegree.rootShearingLogTime`, `OAI.DukePrimeDegree.rootShearingMovingSize`, `OAI.DukePrimeDegree.rootShearingOffDiagonalSize`, `OAI.DukePrimeDegree.rootSliceReindexHomeomorph`, `OAI.DukePrimeDegree.shiftedRootFactorCoordinateMap` and 99 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `DukePrimeDegree_Arithmetic_CyclicInduction`, `DukePrimeDegree_Arithmetic_SubfieldOrders`, `DukePrimeDegree_Arithmetic_ZetaOrder`, `DukePrimeDegree_Dynamics_BlockRootGroup`, `DukePrimeDegree_Dynamics_CentralizerFlow`, `DukePrimeDegree_Dynamics_ConjugationOrbit`, `DukePrimeDegree_Dynamics_LatticeCentralizer`, `DukePrimeDegree_Dynamics_LeafFlowCovariance`, `DukePrimeDegree_Dynamics_MatrixVelocitySpace`, `DukePrimeDegree_Dynamics_MautnerRootPair`, `DukePrimeDegree_Dynamics_OrbitRationality`, `DukePrimeDegree_Dynamics_PrimeBlockRationality`, `DukePrimeDegree_Dynamics_ShearingCompactness`, `DukePrimeDegree_Dynamics_ShearingDiagonal`, `DukePrimeDegree_Dynamics_ShearingHorosphere`, `DukePrimeDegree_Dynamics_ShearingKappa`, `DukePrimeDegree_Dynamics_ShearingLogTime`, `DukePrimeDegree_Dynamics_ShearingScale`, `DukePrimeDegree_Dynamics_SingleBlockCorrectedPairs`, `DukePrimeDegree_Dynamics_SingleBlockErgodicity`, `DukePrimeDegree_Dynamics_SingleBlockNormalization`, `DukePrimeDegree_Dynamics_SingleBlockShell`, `DukePrimeDegree_Dynamics_SmallCentralizer`, `DukePrimeDegree_Dynamics_SmallReturns`, `DukePrimeDegree_Dynamics_StrongReturns`, `DukePrimeDegree_Dynamics_VelocityTransportRank`, `DukePrimeDegree_Entropy_BilateralConditionalSupport`, `DukePrimeDegree_Entropy_BilateralFiniteCodes`, `DukePrimeDegree_Entropy_CountableFutureMap`, `DukePrimeDegree_Entropy_CountableFutureSigma`, `DukePrimeDegree_Entropy_FutureFiberKernel`, `DukePrimeDegree_Entropy_FutureSigmaAlgebra`, `DukePrimeDegree_Entropy_NeutralFiberNames`, `DukePrimeDegree_Entropy_NeutralNameCovers`, `DukePrimeDegree_Geometry_CountableWeakKernel`, `DukePrimeDegree_Geometry_FiniteProjectionFrames`, `DukePrimeDegree_Geometry_LatticeGroupDecomposition`, `DukePrimeDegree_Geometry_LeafMeasurableBad`, `DukePrimeDegree_Geometry_NeutralWeightSpace`, `DukePrimeDegree_Geometry_PositiveRootCoordinates`, `DukePrimeDegree_Geometry_PositiveRootPattern`, `DukePrimeDegree_Geometry_QuotientLiftMeasure`, `DukePrimeDegree_Geometry_QuotientLogDistance`, `DukePrimeDegree_Geometry_ShiftedRootPullback`, `DukePrimeDegree_Geometry_UpperRootDisintegration`, `DukePrimeDegree_Geometry_UpperRootLeafMeasure`, `DukePrimeDegree_Geometry_UpperRootWindows`, `DukePrimeDegree_Geometry_WeylDiagonalAction`, `DukePrimeDegree_Geometry_WeylReindex`, `DukePrimeDegree_Geometry_WeylRootBoxes`, `PrimePackets_AmbientLeaves`, `PrimePackets_ArtinSeries`, `PrimePackets_AtomMass`, `PrimePackets_ConditionalFibers`, `PrimePackets_CongruenceLattices`, `PrimePackets_CoordinateLattices`, `PrimePackets_CosetMeromorphic`, `PrimePackets_GaussianMellin`, `PrimePackets_IdealClasses`, `PrimePackets_IdealNorms`, `PrimePackets_IdealThetaFlow`, `PrimePackets_IdealThetaXi`, `PrimePackets_IntegerEmbeddings`, `PrimePackets_KernelScaling`, `PrimePackets_LatticeTheta`, `PrimePackets_LeafAnchors`, `PrimePackets_LeafNormalization`, `PrimePackets_LeafSupport`, `PrimePackets_LeafTransitions`, `PrimePackets_LocalModels`, `PrimePackets_NormalClosure`, `PrimePackets_ObservationCovers`, `PrimePackets_PacketAlgebra`, `PrimePackets_PacketMoments`, `PrimePackets_PeriodicTheta`, `PrimePackets_RadialIntegrals`, `PrimePackets_RayCharacter`, `PrimePackets_RayDescent`, `PrimePackets_RayEuler`, `PrimePackets_RayRealization`, `PrimePackets_RootCharts`, `PrimePackets_RootLeaves`, `PrimePackets_RootRelations`, `PrimePackets_RootSubgroups`, `PrimePackets_ScalingCovariance`, `PrimePackets_ThetaReflection`, `PrimePackets_ThetaTails`, `PrimePackets_UnitOrbitIntegrals`, `PrimePackets_XiBoundary`, `PrimePackets_ZeroReflection`, `PrimePackets_ZeroSeparation`, `PrimePackets_ZetaDerivatives`, `PrimePackets_ZetaResidues`.
--
--   **Imports.** It imports the published bundle `Def_DukePrimeDegree`; the bundles `OAIQ244Duke000`, `OAIQ244Duke001`, `OAIQ244Duke005`, `OAIQ244Duke006`, `OAIQ244Duke011` and `OAIQ244Duke012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke035` and `OAIQ244Duke036`; the statements `OAI.DukePrimeDegree.exists_bounded_branching_subordinate_observation_with_lifts`, `OAI.DukePrimeDegree.exists_controlled_cover_future_observation`, `OAI.DukePrimeDegree.exists_distinct_equal_leaf_horospherical_pair`, `OAI.DukePrimeDegree.exists_real_character_of_simple_zeta`, `OAI.DukePrimeDegree.exists_separated_exponential_cut_family`, `OAI.DukePrimeDegree.exists_singleBlock_terminal_generic_set`, `OAI.DukePrimeDegree.extension_multiplicity_pos_of_ray_realizations`, `OAI.DukePrimeDegree.fixedFieldMultiplicity_le_extension`, `OAI.DukePrimeDegree.idealCharacter_kernelLaw_of_even_modulus`, `OAI.DukePrimeDegree.measureEntropy_le_of_bilateral_heightClip_bounds`, `OAI.DukePrimeDegree.negative_diagonal_entropy_le_root_sum_of_small_auxiliary`, `OAI.DukePrimeDegree.no_odd_index_positive_zero_of_cyclic_characters`, `OAI.DukePrimeDegree.no_odd_index_zero_sign`, `OAI.PrimeDegreePackets.EvenRayCharacter.continued_eq_dirichlet`, `OAI.PrimeDegreePackets.HeckeMellin.boundedDegree_near_one_zero_real_simple_unique`, `OAI.PrimeDegreePackets.HeckeMellin.completedIdealClassXi_eq`, `OAI.PrimeDegreePackets.HeckeMellin.dedekindXiZeros_ne_one_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.dedekindXiZeros_ne_zero_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.fractionalIdealTheta_mellin_lintegral_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.idealThetaMellin_normalized_real`, `OAI.PrimeDegreePackets.ThetaConstruction.normalizedTheta_hasMellin`, `OAI.PrimeDegreePackets.integrable_weightedIdealUnitOrbits`, `OAI.PrimeDegreePackets.integral_unitOrbitMellinKernel` and `OAI.PrimeDegreePackets.tsum_lintegral_weightedUnitOrbitMellinKernel_ne_top`; the proofs of `OAI.DukePrimeDegree.completedXiGap_of_exceptionalRealZeroExclusion`, `OAI.DukePrimeDegree.diagonal_entropy_zero_of_atomic_positive_roots`, `OAI.DukePrimeDegree.exceptionalRealZeroExclusion_of_ray_realizations`, `OAI.DukePrimeDegree.exists_noncentral_neutral_return_sequence`, `OAI.DukePrimeDegree.exists_separated_exponential_cut_family`, `OAI.DukePrimeDegree.extension_multiplicity_pos_of_ray_realizations`, `OAI.DukePrimeDegree.logRegularized_deriv_bound_of_completedXi_gap`, `OAI.DukePrimeDegree.no_odd_index_positive_zero_of_cyclic_characters`, `OAI.DukePrimeDegree.no_odd_index_zero_sign`, `OAI.PrimeDegreePackets.HeckeMellin.boundedDegree_near_one_zero_real_simple_unique`, `OAI.PrimeDegreePackets.HeckeMellin.completedIdealClassXi_eq`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_conj_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_entire`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_eq_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_functionalEquation_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_hasSubquadraticGrowth`, `OAI.PrimeDegreePackets.HeckeMellin.dedekindXiZeros_ne_one_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.dedekindXiZeros_ne_zero_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.dedekindXi_realZeroPole_nonneg_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.idealThetaMellin_normalized_real`, `OAI.PrimeDegreePackets.HeckeMellin.idealThetaXi_entire`, `OAI.PrimeDegreePackets.HeckeMellin.idealThetaXi_reflection_totallyReal`, `OAI.PrimeDegreePackets.ThetaConstruction.normalizedTheta_hasMellin` and `OAI.PrimeDegreePackets.integrable_weightedIdealUnitOrbits`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.Order.SuccPred.PartialSups
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
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Logic.Encodable.Lattice
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.Piecewise
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.PartialSups
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Prod
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
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke000
import Definitions.Def_OAIQ244Duke001
import Definitions.Def_OAIQ244Duke005
import Definitions.Def_OAIQ244Duke006
import Definitions.Def_OAIQ244Duke011
import Definitions.Def_OAIQ244Duke012

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketAlgebra
attribute [-instance] _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.globalLabels_smul_val
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


def completedReduction {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (completedLattice p M) →+ (Fin n → ZMod (p^k)) where
  toFun x i := PadicInt.toZModPow k ((completedLatticeBasis M hn p).equivFun x i)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

lemma completedReduction_eq_zero_iff {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (k : ℕ) (x : completedLattice p M) :
    completedReduction M hn p k x = 0 ↔
      ∃ y : completedLattice p M, x = (p : PadicInt p)^k • y := by
  let b := completedLatticeBasis M hn p
  constructor
  · intro hx
    have h (i : Fin n) : (p : PadicInt p)^k ∣ b.equivFun x i := by
      have H := congrFun hx i
      change PadicInt.toZModPow k (b.equivFun x i) = 0 at H
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at H
      exact H
    choose y hy using h
    refine ⟨b.equivFun.symm y,?_⟩
    apply b.equivFun.injective
    ext i
    simpa only [map_smul,LinearEquiv.apply_symm_apply,Pi.smul_apply,smul_eq_mul] using hy i
  · rintro ⟨y,rfl⟩
    ext i
    change PadicInt.toZModPow k (b.equivFun ((p : PadicInt p)^k • y) i) = 0
    simp only [map_smul,Pi.smul_apply,smul_eq_mul,map_mul,map_pow,map_natCast]
    rw [← Nat.cast_pow,ZMod.natCast_self,zero_mul]


lemma completionEmbedding_coordinates {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (x : M.carrier) (i : Fin n) :
    (completedLatticeBasis M hn p).equivFun (completionEmbedding M p x) i =
      (M.basis.equivFun x i : PadicInt p) := by
  classical
  conv_lhs => rw [← M.basis.sum_equivFun x]
  simp only [map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply,
    completionEmbedding_basis M hn p, Basis.equivFun_self]
  simp



theorem completedReduction_simultaneous_surjective
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ j, Fact (p j).Prime]
    (hp : Function.Injective p) (k : ι → ℕ)
    (z : ∀ j, Fin n → ZMod ((p j)^(k j))) :
    ∃ x : M.carrier, ∀ j,
      completedReduction M hn (p j) (k j) (completionEmbedding M (p j) x) = z j := by
  classical
  have hc : Pairwise (fun i j => Nat.Coprime ((p i)^(k i)) ((p j)^(k j))) := by
    intro i j hij
    exact ((Nat.coprime_primes (Fact.out : (p i).Prime)
      (Fact.out : (p j).Prime)).mpr (hp.ne hij)).pow _ _
  let e := ZMod.prodEquivPi (fun j => (p j)^(k j)) hc
  have h (i : Fin n) : ∃ a : ℤ, ∀ j, (a : ZMod ((p j)^(k j))) = z j i := by
    obtain ⟨a,ha⟩ := ZMod.intCast_surjective (e.symm (fun j => z j i))
    refine ⟨a,?_⟩
    have H := congrArg e ha
    rw [RingEquiv.apply_symm_apply] at H
    intro j
    have Hj := congrFun H j
    simpa using Hj
  choose a ha using h
  refine ⟨M.basis.equivFun.symm a,?_⟩
  intro j
  ext i
  change PadicInt.toZModPow (k j)
    ((completedLatticeBasis M hn (p j)).equivFun
      (completionEmbedding M (p j) _) i) = z j i
  rw [completionEmbedding_coordinates,LinearEquiv.apply_symm_apply,map_intCast]
  exact ha i j

 

theorem exists_fullLattice_of_between
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (N : Submodule ℤ K) (hNM : N ≤ M.carrier)
    (q : ℕ) (hq : q ≠ 0) (hMq : ∀ x ∈ M.carrier, (q : ℤ) • x ∈ N) :
    ∃ L : FullLattice n K, L.carrier = N := by
  classical
  have hspan : Submodule.span ℚ (N : Set K) = ⊤ := by
    apply top_unique
    rw [← M.spans]
    apply Submodule.span_le.mpr
    intro x hx
    have H := Submodule.smul_mem (Submodule.span ℚ (N : Set K)) ((q : ℚ)⁻¹)
      (Submodule.subset_span (hMq x hx))
    simpa [Algebra.smul_def, hq] using H
  obtain ⟨m,b⟩ := Submodule.basisOfPidOfLE hNM M.basis
  have hlin : LinearIndependent ℚ (fun i => (b i : K)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp
      (b.linearIndependent.map' N.subtype (Submodule.ker_subtype N))
  have hbspan : Submodule.span ℚ (Set.range fun i => (b i : K)) = ⊤ := by
    have H : Submodule.span ℤ (Set.range fun i => (b i : K)) = N := by
      rw [show (Set.range fun i => (b i : K)) =
        N.subtype '' Set.range b by rw [← Set.range_comp]; rfl]
      rw [← Submodule.map_span,b.span_eq,Submodule.map_top,Submodule.range_subtype]
    rw [← Submodule.span_span_of_tower ℤ ℚ,H,hspan]
  have hmn : m = n := by
    let bQ := Basis.mk hlin hbspan.ge
    have H := Module.finrank_eq_card_basis bQ
    simpa [hn] using H.symm
  exact ⟨⟨N,b.reindex (finCongr hmn),hspan⟩,rfl⟩

 

def residueConditions
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    {ι : Type*} (p : ι → ℕ) [∀ j, Fact (p j).Prime] (k : ι → ℕ)
    (H : ∀ j, AddSubgroup (Fin n → ZMod ((p j)^(k j)))) : Submodule ℤ M.carrier where
  carrier := {x | ∀ j, completedReduction M hn (p j) (k j)
    (completionEmbedding M (p j) x) ∈ H j}
  zero_mem' := by intro j; simp
  add_mem' hx hy := by
    intro j
    simpa only [map_add] using (H j).add_mem (hx j) (hy j)
  smul_mem' a x hx := by
    intro j
    simpa only [map_zsmul] using (H j).zsmul_mem (hx j) a

lemma smul_mem_residueConditions
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ j, Fact (p j).Prime] (k : ι → ℕ)
    (H : ∀ j, AddSubgroup (Fin n → ZMod ((p j)^(k j)))) (x : M.carrier) :
    ((∏ j, (p j)^(k j) : ℕ) : ℤ) • x ∈ residueConditions M hn p k H := by
  classical
  intro j
  have hd : (p j)^(k j) ∣ ∏ j, (p j)^(k j) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have hzero : completedReduction M hn (p j) (k j)
      (completionEmbedding M (p j) (((∏ j, (p j)^(k j) : ℕ) : ℤ) • x)) = 0 := by
    ext i
    change PadicInt.toZModPow (k j)
      ((completedLatticeBasis M hn (p j)).equivFun
        (completionEmbedding M (p j) _) i) = 0
    rw [completionEmbedding_coordinates]
    simp only [map_zsmul,Pi.smul_apply,zsmul_eq_mul,Int.cast_mul,Int.cast_natCast,map_mul,map_natCast]
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd,zero_mul]
  rw [hzero]
  exact (H j).zero_mem

 

theorem exists_fullLattice_residueConditions
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ j, Fact (p j).Prime] (k : ι → ℕ)
    (H : ∀ j, AddSubgroup (Fin n → ZMod ((p j)^(k j)))) :
    ∃ L : FullLattice n K, L.carrier ≤ M.carrier ∧
      ∀ x : M.carrier, (x : K) ∈ L.carrier ↔
        ∀ j, completedReduction M hn (p j) (k j)
          (completionEmbedding M (p j) x) ∈ H j := by
  classical
  let N := (residueConditions M hn p k H).map M.carrier.subtype
  have hNM : N ≤ M.carrier := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Submodule.mem_map.mp hx
    exact y.property
  have hq : (∏ j, (p j)^(k j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (Fact.out : (p j).Prime).ne_zero)
  obtain ⟨L,hL⟩ := exists_fullLattice_of_between M hn N hNM _ hq (by
    intro x hx
    exact Submodule.mem_map.mpr ⟨((∏ j, (p j)^(k j) : ℕ) : ℤ) • (⟨x,hx⟩ : M.carrier),
      smul_mem_residueConditions M hn p k H ⟨x,hx⟩,rfl⟩)
  refine ⟨L,hL ▸ hNM,?_⟩
  intro x
  rw [hL]
  change (x : K) ∈ (residueConditions M hn p k H).map M.carrier.subtype ↔ _
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y,hy,hxy⟩
    have : y = x := Subtype.ext hxy
    subst y
    exact hy
  · intro hx
    exact ⟨x,hx,rfl⟩

 

theorem residueConditions_surjective
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ j, Fact (p j).Prime]
    (hp : Function.Injective p) (k : ι → ℕ)
    (H : ∀ j, AddSubgroup (Fin n → ZMod ((p j)^(k j))))
    (z : ∀ j, Fin n → ZMod ((p j)^(k j))) (hz : ∀ j, z j ∈ H j) :
    ∃ x ∈ residueConditions M hn p k H, ∀ j,
      completedReduction M hn (p j) (k j) (completionEmbedding M (p j) x) = z j := by
  obtain ⟨x,hx⟩ := completedReduction_simultaneous_surjective M hn p hp k z
  exact ⟨x,fun j => (hx j).symm ▸ hz j,hx⟩

 

lemma completedReduction_mem_image_iff
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (k : ℕ)
    (N : Submodule (PadicInt p) (completedLattice p M))
    (hN : ∀ y, (p : PadicInt p)^k • y ∈ N) (x : completedLattice p M) :
    completedReduction M hn p k x ∈ N.toAddSubgroup.map (completedReduction M hn p k) ↔
      x ∈ N := by
  constructor
  · rintro ⟨y,hy,hyx⟩
    have H : completedReduction M hn p k (x-y) = 0 := by rw [map_sub,hyx,sub_self]
    obtain ⟨z,hz⟩ := (completedReduction_eq_zero_iff M hn p k _).mp H
    have hd : x-y ∈ N := hz ▸ hN z
    simpa only [sub_add_cancel] using N.add_mem hd hy
  · intro hx
    exact ⟨x,hx,rfl⟩

 
lemma completedLattice_mono
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    {M N : FullLattice n K} (hMN : M.carrier ≤ N.carrier)
    (p : ℕ) [Fact p.Prime] : completedLattice p M ≤ completedLattice p N :=
  Submodule.span_mono (Set.image_mono hMN)

 

lemma completedLattice_smul_mem
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    {M N : FullLattice n K} (q : ℕ)
    (hMN : ∀ x ∈ M.carrier, (q : ℤ) • x ∈ N.carrier)
    (p : ℕ) [Fact p.Prime] {y : LocalAlgebra p K} (hy : y ∈ completedLattice p M) :
    (q : PadicInt p) • y ∈ completedLattice p N := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z,hz,rfl⟩ := hx
    have H : (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K)
        ((q : ℤ) • z) ∈ completedLattice p N := Submodule.subset_span
      (show (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K)
          ((q : ℤ) • z) ∈
        (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) ''
          (N.carrier : Set K) from ⟨(q : ℤ) • z,hMN z hz,rfl⟩)
    simpa only [map_zsmul, map_nsmul, Nat.cast_smul_eq_nsmul] using H
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [smul_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    rw [smul_comm]
    exact Submodule.smul_mem _ _ ih

 

lemma completedLattice_primePower_mem
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    {M N : FullLattice n K} (q : ℕ)
    (hMN : ∀ x ∈ M.carrier, (q : ℤ) • x ∈ N.carrier)
    (p : ℕ) [Fact p.Prime] (k r : ℕ) (hqr : q = p^k*r)
    (hr : Nat.Coprime p r) {y : LocalAlgebra p K} (hy : y ∈ completedLattice p M) :
    (p : PadicInt p)^k • y ∈ completedLattice p N := by
  have hu : IsUnit (r : PadicInt p) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr hr)
  obtain ⟨u,hu⟩ := hu
  have H := Submodule.smul_mem (completedLattice p N) (↑(u⁻¹) : PadicInt p)
    (completedLattice_smul_mem q hMN p hy)
  rw [smul_smul,hqr,Nat.cast_mul,Nat.cast_pow,← hu] at H
  have he : (↑(u⁻¹) : PadicInt p) * ((p : PadicInt p)^k * u) = (p : PadicInt p)^k := by
    rw [mul_left_comm,Units.inv_mul,mul_one]
  rwa [he] at H



theorem patch_fullLattice_completions
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ j, Fact (p j).Prime]
    (hp : Function.Injective p) (k : ι → ℕ)
    (N : ∀ j, Submodule (PadicInt (p j)) (LocalAlgebra (p j) K))
    (hNM : ∀ j, N j ≤ completedLattice (p j) M)
    (hNpow : ∀ j y, y ∈ completedLattice (p j) M → (p j : PadicInt (p j))^(k j) • y ∈ N j) :
    ∃ L : FullLattice n K, L.carrier ≤ M.carrier ∧
      (∀ j, completedLattice (p j) L = N j) ∧
      ∀ (r : ℕ) (hr : r.Prime), letI : Fact r.Prime := ⟨hr⟩;
        r ∉ Set.range p → completedLattice r L = completedLattice r M := by
  classical
  let R (j : ι) := (N j).comap (completedLattice (p j) M).subtype
  let H (j : ι) := (R j).toAddSubgroup.map (completedReduction M hn (p j) (k j))
  have hR (j : ι) (y : completedLattice (p j) M) : (p j : PadicInt (p j))^(k j) • y ∈ R j :=
    hNpow j y y.property
  have hred (j : ι) (x : completedLattice (p j) M) :
      completedReduction M hn (p j) (k j) x ∈ H j ↔ (x : LocalAlgebra (p j) K) ∈ N j :=
    completedReduction_mem_image_iff M hn (p j) (k j) (R j) (hR j) x
  obtain ⟨L,hLM,hL⟩ := exists_fullLattice_residueConditions M hn p k H
  let q := ∏ j, (p j)^(k j)
  have hmul (x : K) (hx : x ∈ M.carrier) : (q : ℤ) • x ∈ L.carrier := by
    exact (hL ((q : ℤ) • (⟨x,hx⟩ : M.carrier))).mpr
      (smul_mem_residueConditions M hn p k H ⟨x,hx⟩)
  have hL' (x : M.carrier) : (x : K) ∈ L.carrier ↔
      ∀ j, (completionEmbedding M (p j) x : LocalAlgebra (p j) K) ∈ N j := by
    rw [hL x]
    exact forall_congr' (fun j => hred j _)
  have hle (j : ι) : completedLattice (p j) L ≤ N j := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    exact (hL' ⟨x,hLM hx⟩).mp hx j
  refine ⟨L,hLM,?_,?_⟩
  · intro j
    apply le_antisymm (hle j)
    intro y hy
    let yM : completedLattice (p j) M := ⟨y,hNM j hy⟩
    let z : ∀ i, Fin n → ZMod ((p i)^(k i)) :=
      Pi.single j (completedReduction M hn (p j) (k j) yM)
    have hz : ∀ i, z i ∈ H i := by
      intro i
      by_cases hij : i = j
      · subst i
        simpa only [z,Pi.single_eq_same] using (hred j yM).mpr hy
      · simpa only [z,Pi.single_eq_of_ne hij] using (H i).zero_mem
    obtain ⟨x,hx,hxz⟩ := residueConditions_surjective M hn p hp k H z hz
    have hxL : (x : K) ∈ L.carrier := (hL x).mpr hx
    have hker : completedReduction M hn (p j) (k j)
        (yM - completionEmbedding M (p j) x) = 0 := by
      rw [map_sub,hxz j]
      simp only [z,Pi.single_eq_same,sub_self]
    obtain ⟨a,ha⟩ := (completedReduction_eq_zero_iff M hn (p j) (k j) _).mp hker
    have hpa : (p j : PadicInt (p j))^(k j) • (a : LocalAlgebra (p j) K) ∈
        completedLattice (p j) L := by
      apply completedLattice_primePower_mem q hmul (p j) (k j)
        (∏ i ∈ Finset.univ.erase j, (p i)^(k i))
      · exact (Finset.mul_prod_erase Finset.univ (fun i => (p i)^(k i))
          (Finset.mem_univ j)).symm
      · exact prime_coprime_other_factors p hp k j
      · exact a.property
    have had : y - (completionEmbedding M (p j) x : LocalAlgebra (p j) K) ∈
        completedLattice (p j) L := by
      have he := congrArg Subtype.val ha
      change y - (completionEmbedding M (p j) x : LocalAlgebra (p j) K) =
        (p j : PadicInt (p j))^(k j) • (a : LocalAlgebra (p j) K) at he
      rw [he]
      exact hpa
    have hxe : (completionEmbedding M (p j) x : LocalAlgebra (p j) K) ∈
        completedLattice (p j) L := Submodule.subset_span ⟨x,hxL,rfl⟩
    simpa only [sub_add_cancel] using (completedLattice (p j) L).add_mem had hxe
  · intro r hr
    let : Fact r.Prime := ⟨hr⟩
    intro hnot
    apply le_antisymm (completedLattice_mono hLM r)
    intro y hy
    have hc : Nat.Coprime r q := by
      apply Nat.Coprime.prod_right
      intro j _
      apply Nat.Coprime.pow_right
      apply (Nat.coprime_primes hr (Fact.out : (p j).Prime)).mpr
      exact fun he => hnot ⟨j,he.symm⟩
    simpa only [pow_zero,one_smul] using
      completedLattice_primePower_mem q hmul r 0 q (by simp) hc hy


lemma fullLatticeRatBasis_repr_integral {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) {x : K} (hx : x ∈ M.carrier)
    (i : Fin n) : ∃ z : ℤ, (fullLatticeRatBasis M hn).repr x i = z := by
  rw [← fullLattice_span_basis M] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      change ∃ z : ℤ, (fullLatticeRatBasis M hn).repr (M.basis j) i = z
      rw [← fullLatticeRatBasis_apply M hn j, Basis.repr_self_apply]
      by_cases h : j = i
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [h]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a + b, by simp [ha, hb]⟩
  | smul a x hx ih =>
      obtain ⟨b, hb⟩ := ih
      refine ⟨a * b, ?_⟩
      rw [map_zsmul, Finsupp.smul_apply, hb]
      simp

 

lemma completedLattice_coordinate_integral {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] {x : LocalAlgebra p K} (hx : x ∈ completedLattice p M)
    (i : Fin n) : ∃ a : PadicInt p,
      ((fullLatticeRatBasis M hn).baseChange (Padic p)).repr x i = (a : Padic p) := by
  let b := (fullLatticeRatBasis M hn).baseChange (Padic p)
  let c := (b.coord i).restrictScalars (PadicInt p)
  change ∃ a : PadicInt p, c x = (a : Padic p)
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      obtain ⟨a, ha⟩ := fullLatticeRatBasis_repr_integral M hn hz i
      refine ⟨a, ?_⟩
      change ((fullLatticeRatBasis M hn).baseChange (Padic p)).repr
        (1 ⊗ₜ[ℚ] z) i = ((a : PadicInt p) : Padic p)
      rw [Basis.baseChange_repr_tmul, ha]
      simp
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a + b, by simp [ha, hb]⟩
  | smul a x hx ih =>
      obtain ⟨b, hb⟩ := ih
      refine ⟨a * b, ?_⟩
      rw [map_smul, hb]
      simp [Algebra.smul_def]

 
theorem mem_fullLattice_iff_forall_completed {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (x : K) :
    x ∈ M.carrier ↔ ∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩;
      Algebra.TensorProduct.includeRight (R := ℚ) (A := Padic p) x ∈ completedLattice p M := by
  constructor
  · intro hx p hp
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  · intro hx
    have hint (i : Fin n) : ∃ a : ℤ, (a : ℚ) = (fullLatticeRatBasis M hn).repr x i := by
      apply rat_integral_of_padic_integral
      intro p hp
      let : Fact p.Prime := ⟨hp⟩
      obtain ⟨a, ha⟩ := completedLattice_coordinate_integral M hn p (hx p hp) i
      simp only [Algebra.TensorProduct.includeRight_apply, Basis.baseChange_repr_tmul,
        Algebra.smul_def, mul_one] at ha
      change ‖((algebraMap ℚ (Padic p)) ((fullLatticeRatBasis M hn).repr x i))‖ ≤ 1
      rw [ha]
      exact a.property
    choose a ha using hint
    have hsum : x = ∑ i, a i • (M.basis i : K) := by
      have h := (fullLatticeRatBasis M hn).sum_repr x
      simp only [← funext_iff] at ha
      rw [← h]
      apply Finset.sum_congr rfl
      intro i _
      rw [← congrFun ha i, fullLatticeRatBasis_apply]
      simp [Algebra.smul_def]
    rw [hsum]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (M.basis i).property)



open scoped NumberField Pointwise nonZeroDivisors
open NumberField


lemma completedFractionalIdeal_fg {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : FractionalIdeal (𝓞 K)⁰ K) :
    (completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K)).FG := by
  classical
  have hI := (FractionalIdeal.fg_of_isNoetherianRing (le_refl (𝓞 K)⁰) I).restrictScalars (R := ℤ)
  obtain ⟨s,hs⟩ := hI
  let f : K →ₐ[ℚ] LocalAlgebra p K := Algebra.TensorProduct.includeRight
  refine ⟨s.image f, le_antisymm ?_ ?_⟩
  · apply Submodule.span_le.mpr
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    apply Submodule.subset_span
    refine ⟨x,?_,rfl⟩
    have hx' : x ∈ Submodule.span ℤ (s : Set K) := Submodule.subset_span hx
    rwa [hs] at hx'
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    change x ∈ (I : Submodule (𝓞 K) K).restrictScalars ℤ at hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨y,hy,rfl⟩))
    | zero => simp
    | add x y hx hy ihx ihy =>
      change f (x+y) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
      change f (a • x) ∈ _
      rw [map_zsmul]
      have H := Submodule.smul_mem
        (Submodule.span (PadicInt p) ((s.image f : Finset (LocalAlgebra p K)) : Set (LocalAlgebra p K)))
        (a : PadicInt p) ih
      simp only [Int.cast_smul_eq_zsmul, f] at H
      exact H

def saturation {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : Submodule ℤ K :=
  (Submodule.span (𝓞 K) (M.carrier : Set K)).restrictScalars ℤ


def saturationIndex {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : ℕ := M.carrier.toAddSubgroup.relIndex (saturation M).toAddSubgroup


abbrev labelPrimes {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) := ↥(saturationIndex M).primeFactors

instance labelPrime_fact {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : labelPrimes M) : Fact p.val.Prime :=
  ⟨(Nat.mem_primeFactors.mp p.property).1⟩



open Topology
open scoped Pointwise
instance instTopologicalSpaceLocalAlgebra {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    TopologicalSpace (LocalAlgebra p K) := moduleTopology (Padic p) (LocalAlgebra p K)
instance instIsModuleTopologyPadicLocalAlgebra {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    IsModuleTopology (Padic p) (LocalAlgebra p K) := ⟨rfl⟩
instance instIsTopologicalRingLocalAlgebra {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    IsTopologicalRing (LocalAlgebra p K) := IsModuleTopology.isTopologicalRing (Padic p) (LocalAlgebra p K)
instance instContinuousSMulPadicLocalAlgebra {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    ContinuousSMul (Padic p) (LocalAlgebra p K) := IsModuleTopology.toContinuousSMul (Padic p) (LocalAlgebra p K)
def localAlgebraCoordinates {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (p : ℕ) [Fact p.Prime] (b : Basis ι ℚ K) : LocalAlgebra p K ≃L[Padic p] (ι → Padic p) where
  __ := (b.baseChange (Padic p)).equivFun
  continuous_toFun := IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := IsModuleTopology.continuous_of_linearMap
    ((b.baseChange (Padic p)).equivFun.symm.toLinearMap)


def localIntegralSpan {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (p : ℕ) [Fact p.Prime] (b : Basis ι ℚ K) : Submodule (PadicInt p) (LocalAlgebra p K) :=
  Submodule.span (PadicInt p) (Set.range (fun i => (b.baseChange (Padic p)) i))

lemma localIntegralSpan_mem {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (p : ℕ) [Fact p.Prime] (b : Basis ι ℚ K) (x : LocalAlgebra p K) :
    x ∈ localIntegralSpan p b ↔ ∀ i, ‖localAlgebraCoordinates p b x i‖ ≤ 1 := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i,rfl⟩ := hy
      intro j
      change ‖(b.baseChange (Padic p)).repr ((b.baseChange (Padic p)) i) j‖ ≤ 1
      rw [Basis.repr_self]
      by_cases h : i = j
      · subst j; simp
      · simp [h]
    | zero => simp [localAlgebraCoordinates]
    | add x y hx hy ihx ihy =>
      intro i
      simpa using (Padic.nonarchimedean (localAlgebraCoordinates p b x i) (localAlgebraCoordinates p b y i)).trans
        (max_le (ihx i) (ihy i))
    | smul a x hx ih =>
      intro i
      have ha : ‖(a : Padic p)‖ ≤ 1 := a.property
      have hsm : localAlgebraCoordinates p b (a • x) i = (a : Padic p) * localAlgebraCoordinates p b x i := by
        change (b.baseChange (Padic p)).repr (a • x) i = _
        rw [← IsScalarTower.algebraMap_smul (Padic p) a x,map_smul]
        rfl
      rw [hsm,norm_mul]
      exact (mul_le_mul ha (ih i) (norm_nonneg _) zero_le_one).trans (by norm_num)
  · intro hx
    rw [← (b.baseChange (Padic p)).sum_repr x]
    apply Submodule.sum_mem
    intro i _
    let a : PadicInt p := ⟨localAlgebraCoordinates p b x i,hx i⟩
    have h := Submodule.smul_mem (localIntegralSpan p b) a
      (Submodule.subset_span (Set.mem_range_self i))
    rw [← IsScalarTower.algebraMap_smul (Padic p) a] at h
    exact h

lemma localIntegralSpan_open {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (p : ℕ) [Fact p.Prime] (b : Basis ι ℚ K) :
    IsOpen (localIntegralSpan p b : Set (LocalAlgebra p K)) := by
  have he : (localIntegralSpan p b : Set (LocalAlgebra p K)) =
      ⋂ i, (fun x => localAlgebraCoordinates p b x i) ⁻¹' Set.range ((↑) : PadicInt p → Padic p) := by
    ext x
    rw [SetLike.mem_coe,localIntegralSpan_mem]
    simp only [Set.mem_iInter,Set.mem_preimage,Subtype.range_coe_subtype]
    rfl
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact PadicInt.isOpenEmbedding_coe.isOpen_range.preimage
    ((continuous_apply i).comp (localAlgebraCoordinates p b).continuous)



lemma completedLattice_open {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime] :
    IsOpen (completedLattice p M : Set (LocalAlgebra p K)) := by
  have h := localIntegralSpan_open p (fullLatticeRatBasis M hn)
  simpa [localIntegralSpan,completedLattice_eq_span_basis] using h

open Filter in
 

lemma localModule_denominator {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (S : Submodule (PadicInt p) (LocalAlgebra p K))
    (hS : S.FG) : ∃ k : ℕ, ∀ x ∈ S,
      (p : PadicInt p)^k • x ∈ (completedMaximalOrder (K := K) p).toSubmodule := by
  let R := (completedMaximalOrder (K := K) p).toSubmodule
  have hRo : IsOpen (R : Set (LocalAlgebra p K)) := by
    exact completedLattice_open (fractionalIdealFullLattice (K := K) rfl 1) rfl p
  have hpow : Tendsto (fun k : ℕ => (p : Padic p)^k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      rw [Padic.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))
  have hx (x : LocalAlgebra p K) : ∀ᶠ k : ℕ in atTop, (p : PadicInt p)^k • x ∈ R := by
    have H : ∀ᶠ k : ℕ in atTop, (p : Padic p)^k • x ∈ R :=
      (hpow.smul tendsto_const_nhds).eventually
        (hRo.mem_nhds (show (0 : Padic p) • x ∈ R by simp))
    filter_upwards [H] with k hk
    rw [← IsScalarTower.algebraMap_smul (Padic p),map_pow,map_natCast]
    exact hk
  obtain ⟨t,ht⟩ := hS
  have ht' : ∀ᶠ k : ℕ in atTop, ∀ x ∈ t, (p : PadicInt p)^k • x ∈ R := by
    exact (Filter.eventually_all_finset t).mpr (fun x _ => hx x)
  obtain ⟨k,hk⟩ := ht'.exists
  refine ⟨k,?_⟩
  intro x hx
  rw [←ht] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hk x hx
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [smul_add] using R.add_mem ihx ihy
  | smul a x hx ih => simpa only [smul_comm ((p : PadicInt p)^k) a] using R.smul_mem a ih

lemma completedLattice_scale_rat {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a : ℚˣ) (p : ℕ) [Fact p.Prime] :
    completedLattice p (scaleFullLattice M (Units.map (algebraMap ℚ K) a)) =
      (algebraMap ℚ (Padic p) (a : ℚ)) • completedLattice p M := by
  rw [completedLattice_scale, Submodule.pointwise_smul_def]
  congr 1
  ext x
  change (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K)
    (algebraMap ℚ K (a : ℚ)) * x = (algebraMap ℚ (Padic p) (a : ℚ)) • x
  rw [AlgHom.commutes,← IsScalarTower.algebraMap_smul (LocalAlgebra p K),
    IsScalarTower.algebraMap_apply ℚ (Padic p) (LocalAlgebra p K)]
  rfl

 

lemma patch_localOvermodule {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (S : Submodule (PadicInt p) (LocalAlgebra p K))
    (hS : S.FG) (hRS : (completedMaximalOrder (K := K) p).toSubmodule ≤ S) :
    ∃ L : FullLattice (Module.finrank ℚ K) K,
      completedLattice p L = S ∧
      ∀ (r : ℕ) (hr : r.Prime), letI : Fact r.Prime := ⟨hr⟩;
        r ≠ p → completedLattice r L = (completedMaximalOrder (K := K) r).toSubmodule := by
  classical
  obtain ⟨k,hk⟩ := localModule_denominator p S hS
  let M := fractionalIdealFullLattice (K := K) rfl (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  let N : Submodule (PadicInt p) (LocalAlgebra p K) := (p : Padic p)^k • S
  have hN : N ≤ completedLattice p M := by
    rintro x hx
    obtain ⟨y,hy,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    have H := hk y hy
    rw [← IsScalarTower.algebraMap_smul (Padic p),map_pow,map_natCast] at H
    exact H
  have hpow (x : LocalAlgebra p K) (hx : x ∈ completedLattice p M) :
      (p : PadicInt p)^k • x ∈ N := by
    rw [← IsScalarTower.algebraMap_smul (Padic p),map_pow,map_natCast]
    exact Submodule.smul_mem_pointwise_smul x _ S (hRS hx)
  obtain ⟨L,hLM,hLp,hLoff⟩ := patch_fullLattice_completions M rfl
    (fun _ : Unit => p) (fun _ _ _ => Subsingleton.elim _ _) (fun _ => k) (fun _ => N)
    (fun _ => hN) (fun _ => hpow)
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  let a : ℚˣ := (Units.mk0 (p : ℚ) hp0)^(- (k : ℤ))
  have ha (r : ℕ) [Fact r.Prime] : algebraMap ℚ (Padic r) (a : ℚ) = ((p : Padic r)^k)⁻¹ := by
    simp [a, zpow_neg, zpow_natCast]
  refine ⟨scaleFullLattice L (Units.map (algebraMap ℚ K) a),?_,?_⟩
  · rw [completedLattice_scale_rat,ha,hLp ()]
    change ((p : Padic p)^k)⁻¹ • ((p : Padic p)^k • S) = S
    rw [inv_smul_smul₀ (pow_ne_zero k (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))]
  · intro r hr hrp
    let : Fact r.Prime := ⟨hr⟩
    rw [completedLattice_scale_rat,ha,hLoff r hr (by simpa using hrp)]
    have hc : r.Coprime p := (Nat.coprime_primes hr (Fact.out : p.Prime)).mpr hrp
    obtain ⟨u,hu⟩ := (PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hc))
    have he : ((p : Padic r)^k)⁻¹ =
        algebraMap (PadicInt r) (Padic r) ((↑(u⁻¹)^k : PadicInt r)) := by
      rw [map_pow,map_units_inv,hu,map_natCast,inv_pow]
    rw [he]
    have hs (b : PadicInt r) :
        (algebraMap (PadicInt r) (Padic r) b) • completedLattice r M = b • completedLattice r M := by
      simp only [Submodule.pointwise_smul_def]
      congr 1
    rw [hs]
    change ((↑(u⁻¹)^k : PadicInt r)) • (completedMaximalOrder (K := K) r).toSubmodule = _
    let R := (completedMaximalOrder (K := K) r).toSubmodule
    apply le_antisymm (Submodule.smul_le_self_of_tower _ _)
    intro x hx
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨(u : PadicInt r)^k • x,R.smul_mem _ hx,?_⟩
    rw [smul_smul,← mul_pow,Units.inv_mul,one_pow,one_smul]

 

theorem completedMaximalOrder_maximal_finite {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (S : Subalgebra (PadicInt p) (LocalAlgebra p K))
    (hS : S.toSubmodule.FG) (hRS : completedMaximalOrder (K := K) p ≤ S) :
    S = completedMaximalOrder (K := K) p := by
  classical
  obtain ⟨L,hLp,hLoff⟩ := patch_localOvermodule p S.toSubmodule hS hRS
  have h1 : (1 : K) ∈ L.carrier := by
    rw [mem_fullLattice_iff_forall_completed L rfl]
    intro r hr
    let : Fact r.Prime := ⟨hr⟩
    rw [map_one]
    by_cases he : r = p
    · subst r
      rw [hLp]
      exact S.one_mem
    · rw [hLoff r hr he]
      exact (completedMaximalOrder (K := K) r).one_mem
  have hmul (x y : K) (hx : x ∈ L.carrier) (hy : y ∈ L.carrier) : x*y ∈ L.carrier := by
    rw [mem_fullLattice_iff_forall_completed L rfl] at hx hy ⊢
    intro r hr
    let : Fact r.Prime := ⟨hr⟩
    have hx' := hx r hr
    have hy' := hy r hr
    rw [map_mul]
    by_cases he : r = p
    · subst r
      rw [hLp] at hx' hy' ⊢
      exact S.mul_mem hx' hy'
    · rw [hLoff r hr he] at hx' hy' ⊢
      exact (completedMaximalOrder (K := K) r).mul_mem hx' hy'
  let T : Subalgebra ℤ K :=
    { carrier := L.carrier
      zero_mem' := L.carrier.zero_mem
      add_mem' := L.carrier.add_mem
      mul_mem' := hmul _ _
      algebraMap_mem' := fun z => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact L.carrier.smul_mem z h1 }
  have hTL : T.toSubmodule = L.carrier := by ext x; rfl
  have hfg : T.toSubmodule.FG := by
    rw [hTL]
    refine ⟨Finset.univ.image (fun i => (L.basis i : K)),?_⟩
    simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ] using fullLattice_span_basis L
  let M := fractionalIdealFullLattice (K := K) rfl (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  have hLM : L.carrier ≤ M.carrier := by
    intro x hx
    have hint := IsIntegral.of_mem_of_fg T hfg x hx
    change x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K)
    exact (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mpr ⟨⟨x,hint⟩,rfl⟩
  have H := completedLattice_mono hLM p
  rw [hLp] at H
  exact le_antisymm H hRS

 

theorem mem_completedMaximalOrder_iff_isIntegral {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (x : LocalAlgebra p K) :
    x ∈ completedMaximalOrder (K := K) p ↔ IsIntegral (PadicInt p) x := by
  let R := completedMaximalOrder (K := K) p
  have hR : R.toSubmodule.FG := completedFractionalIdeal_fg p 1
  constructor
  · exact IsIntegral.of_mem_of_fg R hR x
  · intro hx
    let : Module.Finite (PadicInt p) R := Module.Finite.of_fg hR
    let T := Algebra.adjoin R ({x} : Set (LocalAlgebra p K))
    have hT : T.toSubmodule.FG := (hx.tower_top (A := R)).fg_adjoin_singleton
    have hRT : R ≤ T.restrictScalars (PadicInt p) := by
      intro y hy
      exact T.algebraMap_mem (⟨y,hy⟩ : R)
    have he := completedMaximalOrder_maximal_finite p (T.restrictScalars (PadicInt p))
      (hT.restrictScalars (R := PadicInt p)) hRT
    have hxT : x ∈ T := Algebra.subset_adjoin (Set.mem_singleton x)
    have hxT' : x ∈ T.restrictScalars (PadicInt p) := hxT
    exact he ▸ hxT' 

theorem completedMaximalOrder_eq_integralClosure {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    completedMaximalOrder (K := K) p = integralClosure (PadicInt p) (LocalAlgebra p K) := by
  ext x
  exact mem_completedMaximalOrder_iff_isIntegral p x

open Polynomial



open scoped NNReal

open Polynomial
open scoped BigOperators


lemma localAlgebra_etale (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K] :
    Algebra.Etale (Padic p) (LocalAlgebra p K) := by
  let : Algebra.FormallyEtale ℚ K := Algebra.FormallyEtale.of_isSeparable ℚ K
  let : Algebra.Etale ℚ K :=
    { finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

 
theorem localAlgebra_exists_product (p : ℕ) [Fact p.Prime] (K : Type u)
    [Field K] [NumberField K] :
    ∃ (I : Type u) (_ : Finite I) (E : I → Type u) (_ : ∀ i, Field (E i))
      (_ : ∀ i, Algebra (Padic p) (E i))
      (_ : ∀ i, FiniteDimensional (Padic p) (E i)),
      Nonempty (LocalAlgebra p K ≃ₐ[Padic p] Π i, E i) := by
  let : Algebra.Etale (Padic p) (LocalAlgebra p K) := localAlgebra_etale p K
  obtain ⟨I,hI,E,hE,hA,e,hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod (Padic p) (LocalAlgebra p K)).mp
      inferInstance
  let : FiniteDimensional (Padic p) (∀ i, E i) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  have hdim (i : I) : FiniteDimensional (Padic p) (E i) :=
    Module.Finite.of_surjective (LinearMap.proj i) (Function.surjective_eval i)
  exact ⟨I,hI,E,hE,hA,hdim,⟨e⟩⟩

open IsDiscreteValuationRing IsLocalRing Module

 
lemma cardQuot_span_prime_of_free (p : ℕ) [Fact p.Prime]
    (R : Type*) [CommRing R] [Algebra (PadicInt p) R]
    [Module.Free (PadicInt p) R] [Module.Finite (PadicInt p) R] :
    (Ideal.span {(p : R)}).cardQuot = p ^ Module.finrank (PadicInt p) R := by
  classical
  let b := Module.Free.chooseBasis (PadicInt p) R
  let h : R →+ (Module.Free.ChooseBasisIndex (PadicInt p) R → ZMod p) :=
    { toFun := fun x i => PadicInt.toZMod (b.equivFun x i)
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; simp }
  have hs : Function.Surjective h := by
    intro x
    choose y hy using fun i => ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) (x i)
    refine ⟨b.equivFun.symm y,?_⟩
    ext i
    change PadicInt.toZMod (b.equivFun (b.equivFun.symm y) i) = x i
    rw [LinearEquiv.apply_symm_apply]
    exact hy i
  have hsm (x : R) : (p : R) * x = (p : PadicInt p) • x := by simp [Algebra.smul_def]
  have hk : h.ker = (Ideal.span {(p : R)}).toAddSubgroup := by
    ext x
    change h x = 0 ↔ x ∈ Ideal.span {(p : R)}
    rw [Ideal.mem_span_singleton]
    constructor
    · intro hx
      have hd (i) : (p : PadicInt p) ∣ b.equivFun x i := by
        have H := congrFun hx i
        change PadicInt.toZMod (b.equivFun x i) = 0 at H
        rw [← RingHom.mem_ker,PadicInt.ker_toZMod,PadicInt.maximalIdeal_eq_span_p,
          Ideal.mem_span_singleton] at H
        exact H
      choose y hy using hd
      refine ⟨b.equivFun.symm y,?_⟩
      change x = (p : R) * b.equivFun.symm y
      rw [hsm]
      apply b.equivFun.injective
      ext i
      simpa only [map_smul,LinearEquiv.apply_symm_apply,Pi.smul_apply,smul_eq_mul] using hy i
    · rintro ⟨y,rfl⟩
      ext i
      change PadicInt.toZMod (b.equivFun ((p : R) * y) i) = 0
      rw [hsm]
      simp only [map_smul,Pi.smul_apply,smul_eq_mul,map_mul,map_natCast,ZMod.natCast_self,zero_mul]
  change (Ideal.span {(p : R)}).toAddSubgroup.index = _
  rw [← hk,AddSubgroup.index_ker,AddMonoidHom.range_eq_top.mpr hs]
  simp [Module.finrank_eq_card_basis b]


def completedLocalIntegralEquiv
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]
    {I : Type u} [Finite I] (E : I → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra (Padic p) (E i)] [∀ i, Algebra (PadicInt p) (E i)]
    [∀ i, IsScalarTower (PadicInt p) (Padic p) (E i)]
    (e : LocalAlgebra p K ≃ₐ[Padic p] Π i, E i) :
    completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] Π i, integralClosure (PadicInt p) (E i) :=
  (Subalgebra.equivOfEq _ _ (completedMaximalOrder_eq_integralClosure p)).trans
    ((integralClosureEquiv (e.restrictScalars (PadicInt p))).trans
      (integralClosurePiEquiv E))

lemma continuous_completedLocalIntegralEquiv
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]
    {I : Type u} [Finite I] (E : I → Type u) [∀ i, NormedField (E i)]
    [∀ i, NormedAlgebra (Padic p) (E i)] [∀ i, Algebra (PadicInt p) (E i)]
    [∀ i, IsScalarTower (PadicInt p) (Padic p) (E i)]
    (e : LocalAlgebra p K ≃ₐ[Padic p] Π i, E i) :
    Continuous (completedLocalIntegralEquiv p K E e) := by
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  apply continuous_pi
  intro i
  exact ((continuous_apply i).comp (hc.comp continuous_subtype_val)).subtype_mk _

lemma continuous_completedLocalIntegralEquiv_symm
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]
    {I : Type u} [Finite I] (E : I → Type u) [∀ i, NormedField (E i)]
    [∀ i, NormedAlgebra (Padic p) (E i)] [∀ i, Algebra (PadicInt p) (E i)]
    [∀ i, IsScalarTower (PadicInt p) (Padic p) (E i)]
    [∀ i, FiniteDimensional (Padic p) (E i)]
    (e : LocalAlgebra p K ≃ₐ[Padic p] Π i, E i) :
    Continuous (completedLocalIntegralEquiv p K E e).symm := by
  let : Fintype I := Fintype.ofFinite I
  let (i : I) : IsModuleTopology (Padic p) (E i) := isModuleTopologyOfFiniteDimensional
  have hc : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  exact (hc.comp (continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i)))).subtype_mk _

instance completedMaximalOrderModuleFinite
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] :
    Module.Finite (PadicInt p) (completedMaximalOrder (K := K) p) :=
  Module.Finite.of_fg (completedFractionalIdeal_fg p (1 : FractionalIdeal (𝓞 K)⁰ K))

lemma completedMaximalOrder_finrank
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] :
    Module.finrank (PadicInt p) (completedMaximalOrder (K := K) p) = Module.finrank ℚ K := by
  let M := fractionalIdealFullLattice (K := K) rfl (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  let e : completedLattice p M ≃ₗ[PadicInt p] completedMaximalOrder (K := K) p :=
    { toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  simpa only [Fintype.card_fin] using
    Module.finrank_eq_card_basis ((completedLatticeBasis M rfl p).map e)

 

theorem completedMaximalOrder_exists_topological_dvr_product
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K] :
    ∃ (I : Type u) (_ : Finite I) (R : I → Type u) (_ : ∀ i, CommRing (R i))
      (_ : ∀ i, IsDomain (R i)) (_ : ∀ i, IsDiscreteValuationRing (R i))
      (_ : ∀ i, Algebra (PadicInt p) (R i))
      (_ : ∀ i, Finite (IsLocalRing.ResidueField (R i)))
      (_ : ∀ i, TopologicalSpace (R i)) (_ : ∀ i, IsTopologicalRing (R i))
      (_ : ∀ i, CompactSpace (R i)) (_ : ∀ i, T2Space (R i))
      (_ : ∀ i, SecondCountableTopology (R i))
      (_ : ∀ i, Module.Finite (PadicInt p) (R i))
      (_ : ∀ i, FaithfulSMul (PadicInt p) (R i))
      (e : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] Π i, R i),
      Continuous e ∧ Continuous e.symm := by
  obtain ⟨I,hI,E,hE,hA,hdim,⟨e⟩⟩ := localAlgebra_exists_product p K
  let (i : I) : Algebra (PadicInt p) (E i) :=
    ((algebraMap (Padic p) (E i)).comp (algebraMap (PadicInt p) (Padic p))).toAlgebra
  let (i : I) : IsScalarTower (PadicInt p) (Padic p) (E i) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let (i : I) : NontriviallyNormedField (E i) := spectralNorm.nontriviallyNormedField (Padic p) (E i)
  let (i : I) : NormedAlgebra (Padic p) (E i) := spectralNorm.normedAlgebra (Padic p) (E i)
  let (i : I) : IsUltrametricDist (E i) := IsUltrametricDist.of_normedAlgebra (Padic p)
  let (i : I) : ProperSpace (E i) := FiniteDimensional.proper (Padic p) (E i)
  let (i : I) : SecondCountableTopology (E i) := by
    let b := Module.Free.chooseBasis (Padic p) (E i)
    let h : (E i) ≃L[Padic p] (Module.Free.ChooseBasisIndex (Padic p) (E i) → Padic p) :=
      b.equivFun.toContinuousLinearEquiv
    exact h.toHomeomorph.secondCountableTopology
  let R (i : I) : Type u := integralClosure (PadicInt p) (E i)
  let (i : I) : CompactSpace (R i) := compactSpace_integralClosure_padic (E i) p
  let eR := completedLocalIntegralEquiv p K E e
  let (i : I) : Module.Finite (PadicInt p) (R i) := by
    let h : completedMaximalOrder (K := K) p →ₗ[PadicInt p] R i :=
      (LinearMap.proj i).comp eR.toLinearMap
    apply Module.Finite.of_surjective h
    intro x
    classical
    exact ⟨eR.symm (Function.update (fun _ => 0) i x), by simp [h]⟩
  let (i : I) : FaithfulSMul (PadicInt p) (R i) := by
    apply (faithfulSMul_iff_algebraMap_injective _ _).mpr
    intro x y hxy
    have hxy' := congrArg (fun x : R i => (x : E i)) hxy
    change algebraMap (PadicInt p) (E i) x = algebraMap (PadicInt p) (E i) y at hxy'
    exact Subtype.coe_injective ((algebraMap (Padic p) (E i)).injective hxy')
  refine ⟨I,hI,R,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    completedLocalIntegralEquiv p K E e,?_,?_⟩
  · exact continuous_completedLocalIntegralEquiv p K E e
  · exact continuous_completedLocalIntegralEquiv_symm p K E e



open MeasureTheory
open scoped ENNReal

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalModels
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

 

structure ActualLocalModel (p : ℕ) [Fact p.Prime] (K : Type u)
    [Field K] [NumberField K] where
  Index : Type u
  fintype : Fintype Index
  Ring : Index → Type u
  commRing : ∀ i, CommRing (Ring i)
  domain : ∀ i, IsDomain (Ring i)
  dvr : ∀ i, IsDiscreteValuationRing (Ring i)
  algebra : ∀ i, Algebra (PadicInt p) (Ring i)
  finiteResidue : ∀ i, Finite (IsLocalRing.ResidueField (Ring i))
  topology : ∀ i, TopologicalSpace (Ring i)
  topRing : ∀ i, IsTopologicalRing (Ring i)
  compactSpace : ∀ i, CompactSpace (Ring i)
  t2Space : ∀ i, T2Space (Ring i)
  secondCountable : ∀ i, SecondCountableTopology (Ring i)
  equiv : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] ∀ i, Ring i
  e : Index → ℕ
  f : Index → ℕ
  continuous_equiv : Continuous equiv
  continuous_symm : Continuous equiv.symm
  e_pos : ∀ i, 0 < e i
  f_pos : ∀ i, 0 < f i
  valuation_p : ∀ i, addVal (Ring i) (algebraMap (PadicInt p) (Ring i) p) = e i
  card_residue : ∀ i, Nat.card (IsLocalRing.ResidueField (Ring i)) = p ^ f i
  degree : ∑ i, f i * e i = Module.finrank ℚ K

attribute [instance] ActualLocalModel.fintype ActualLocalModel.commRing
  ActualLocalModel.domain ActualLocalModel.dvr ActualLocalModel.algebra
  ActualLocalModel.finiteResidue ActualLocalModel.topology ActualLocalModel.topRing
  ActualLocalModel.compactSpace ActualLocalModel.t2Space ActualLocalModel.secondCountable

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaResidues
attribute [-instance] _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
namespace PrimeDegreePackets

open scoped NumberField nonZeroDivisors



lemma mem_orderedLogSubgroup {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d + 1) K)
    (S : Subgroup (𝓞 K)ˣ) (v : Fin d → ℝ) :
    v ∈ orderedLogSubgroup σ S ↔ ∃ u ∈ S, orderedUnitLog σ (Additive.ofMul u) = v := by
  change (orderedLogCoordinatesEquiv σ).symm v ∈ logSubgroup S ↔ _
  constructor
  · intro hv
    obtain ⟨u, hu, heq⟩ := Submodule.mem_map.mp hv
    refine ⟨u.toMul, hu, ?_⟩
    change orderedLogCoordinatesEquiv σ (NumberField.Units.logEmbedding K u) = v
    change NumberField.Units.logEmbedding K u = (orderedLogCoordinatesEquiv σ).symm v at heq
    rw [heq, LinearEquiv.apply_symm_apply]
  · rintro ⟨u, hu, rfl⟩
    change (orderedLogCoordinatesEquiv σ).symm
      (orderedLogCoordinatesEquiv σ (NumberField.Units.logEmbedding K (Additive.ofMul u))) ∈ _
    rw [LinearEquiv.symm_apply_apply]
    exact Submodule.mem_map.mpr ⟨Additive.ofMul u, hu, rfl⟩



lemma exists_int_matrix_of_rowLattice_le {n : ℕ}
    (g h : Matrix (Fin n) (Fin n) ℝ) (hgh : rowLattice g ≤ rowLattice h) :
    ∃ A : Matrix (Fin n) (Fin n) ℤ, g = A.map (Int.castRingHom ℝ) * h := by
  have H (i : Fin n) : ∃ c : Fin n → ℤ, ∑ j, c j • h j = g i :=
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hgh (Submodule.subset_span ⟨i, rfl⟩))
  choose A hA using H
  refine ⟨A, ?_⟩
  ext i j
  have h := congrFun (hA i) j
  change g i j = ∑ k, (A i k : ℝ) * _
  simpa [Finset.sum_apply, zsmul_eq_mul] using h.symm



def diagonalLinear (n : ℕ) (t : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℤ] (Fin n → ℝ) where
  toFun x i := t i * x i
  map_add' x y := by ext i; exact mul_add _ _ _
  map_smul' z x := by ext i; simp [mul_assoc, mul_comm]

lemma rowLattice_mul_diagonal {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (t : Fin n → ℝ) :
    rowLattice (B * Matrix.diagonal t) = (rowLattice B).map (diagonalLinear n t) := by
  unfold rowLattice
  rw [Submodule.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span ℤ)
  apply congrArg Set.range
  ext i j
  simp [diagonalLinear, Matrix.mul_diagonal, mul_comm]

open scoped Pointwise



open FractionalIdeal

 

theorem fractionalIdeal_same_class {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (I J : (FractionalIdeal R⁰ K)ˣ) :
    ClassGroup.mk K I = ClassGroup.mk K J ↔
      ∃ x : K, x ≠ 0 ∧ FractionalIdeal.spanSingleton R⁰ x * (I : FractionalIdeal R⁰ K) = J := by
  refine (ClassGroup.equiv K).injective.eq_iff.symm.trans ?_
  simp only [ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self,
    Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv, RingEquiv.refl_apply,
    QuotientGroup.mk'_eq_mk', mem_principal_ideals_iff, Units.ext_iff, Units.val_mul,
    Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv, RingEquiv.refl_apply]
  constructor
  · rintro ⟨X, ⟨x, hX⟩, hx⟩
    refine ⟨x, ?_, ?_⟩
    · rintro rfl
      simp [X.ne_zero.symm] at hX
    · simpa only [hX, mul_comm] using hx
  · rintro ⟨x, hx, heq⟩
    refine ⟨toPrincipalIdeal R K (Units.mk0 x hx), ⟨x, by simp⟩, ?_⟩
    simpa only [coe_toPrincipalIdeal, Units.val_mk0, mul_comm] using heq



lemma abs_det_le_of_rowLattice_le {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.det ≠ 0) (hBC : rowLattice B ≤ rowLattice C) : |C.det| ≤ |B.det| := by
  obtain ⟨A, hA⟩ := exists_int_matrix_of_rowLattice_le B C hBC
  have hd : B.det = (A.det : ℝ) * C.det := by
    rw [hA, Matrix.det_mul]
    congr 1
    exact (Int.castRingHom ℝ).map_det A |>.symm
  have hA0 : A.det ≠ 0 := by
    intro h
    rw [h, Int.cast_zero, zero_mul] at hd
    exact hB hd
  have hone : (1 : ℝ) ≤ |(A.det : ℝ)| := by exact_mod_cast Int.one_le_abs hA0
  rw [hd, abs_mul]
  nlinarith [abs_nonneg C.det]

lemma abs_det_eq_of_rowLattice_eq {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.det ≠ 0) (hC : C.det ≠ 0) (hBC : rowLattice B = rowLattice C) :
    |B.det| = |C.det| :=
  le_antisymm (abs_det_le_of_rowLattice_le C B hC hBC.ge)
    (abs_det_le_of_rowLattice_le B C hB hBC.le)



lemma signValue_pow_odd (w : SignTypeˣ) {n : ℕ} (hn : Odd n) : signValue w ^ n = signValue w := by
  rw [signValue_apply, ← SignType.coe_pow, SignType.pow_odd _ hn]



lemma pointLattice_rightAction_diagonal {n : ℕ} (x : X n) (D : G n) (t : Fin n → ℝ)
    (hD : D.1 = Matrix.diagonal t) :
    pointLattice (rightAction x D) = (pointLattice x).map (diagonalLinear n t) := by
  induction x using Quotient.inductionOn with
  | h g =>
    change rowLattice (g.1*D.1) = (rowLattice g.1).map _
    rw [hD,rowLattice_mul_diagonal]



theorem relativeElementClassMap_surjective {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Function.Surjective (relativeElementClassMap I) := by
  intro J
  have hclass : ClassGroup.mk K I⁻¹ = ClassGroup.mk K J.val := by rw [map_inv,J.property.2]
  obtain ⟨a,ha,h⟩ := (fractionalIdeal_same_class I⁻¹ J.val).mp hclass
  have he : relativeElementIdeal I (Units.mk0 a ha) = J.val := by
    apply Units.ext
    simpa only [relativeElementIdeal,Units.val_mul,coe_toPrincipalIdeal,Units.val_mk0] using h
  refine ⟨⟨Units.mk0 a ha,?_⟩,Subtype.ext he⟩
  apply (relativeElementIdeal_le_one_iff I _).mp
  rw [he]
  exact J.property.1

 

def idealElementRepresentative {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (J : integralIdealClassFiber I) : nonzeroIdealElements I :=
  (relativeElementClassMap_surjective I J).choose

lemma idealElementRepresentative_spec {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (J : integralIdealClassFiber I) :
    relativeElementClassMap I (idealElementRepresentative I J) = J :=
  (relativeElementClassMap_surjective I J).choose_spec



def integralFractionalIdealsEquiv (K : Type*) [Field K] [NumberField K] :
    {J : Ideal (𝓞 K) // J ≠ ⊥} ≃ integralFractionalIdeals K :=
  Equiv.ofBijective (fun J =>
    ⟨Units.mk0 (J.1 : FractionalIdeal (𝓞 K)⁰ K) (by simpa using J.2),FractionalIdeal.coeIdeal_le_one⟩)
    ⟨by
      intro J L h
      apply Subtype.ext
      apply FractionalIdeal.coeIdeal_injective (K := K)
      exact congrArg (fun a : integralFractionalIdeals K => a.1.val) h,
    by
      rintro ⟨J,hJ⟩
      obtain ⟨I,hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ
      have hI0 : I ≠ ⊥ := by
        intro he
        subst I
        simp only [FractionalIdeal.coeIdeal_bot] at hI
        exact J.ne_zero hI.symm
      refine ⟨⟨I,hI0⟩,?_⟩
      apply Subtype.ext
      apply Units.ext
      exact hI⟩

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketMoments
attribute [-instance] _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]



theorem exists_integer_row_no_zero_coordinate {n : ℕ} (g : G n) :
    ∃ z : Fin n → ℤ, ∀ j,
      ((fun i => (z i : ℝ)) ᵥ* g.1) j ≠ 0 := by
  let p (j : Fin n) : Polynomial ℝ := ∑ i : Fin n, Polynomial.monomial i.val (g.1 i j)
  have hcoeff (i j : Fin n) : (p j).coeff i.val = g.1 i j := by
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      have hne : b.val ≠ i.val := fun e => hbi (Fin.ext e)
      simp only [hne, ite_false, if_false]
    · simp
  have hp (j : Fin n) : p j ≠ 0 := by
    intro hp
    have hz (i : Fin n) : g.1 i j = 0 := by rw [←hcoeff i j, hp]; simp
    have H := congrArg (fun q : G n => q.1 j j) (inv_mul_cancel g)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      Matrix.mul_apply, Matrix.one_apply_eq] at H
    simp only [hz, mul_zero, Finset.sum_const_zero] at H
    exact zero_ne_one H
  have hfin : (⋃ j, {t | (p j).IsRoot t}).Finite :=
    Set.finite_iUnion (fun j => Polynomial.finite_setOfPred_isRoot (hp j))
  have hinf : (Set.range (fun z : ℤ => (z : ℝ))).Infinite :=
    Set.infinite_range_of_injective Int.cast_injective
  obtain ⟨t,⟨N,rfl⟩, hN⟩ := hinf.exists_notMem_finite hfin
  refine ⟨fun i => N ^ i.val, fun j hj => hN ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨j, ?_⟩
  change (p j).eval (N : ℝ) = 0
  simpa only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    Matrix.vecMul, dotProduct, Int.cast_pow, mul_comm] using hj

 

def vectorEnvelope (n k : ℕ) : Set (X n) :=
  {x | ∃ g : G n, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) g = x ∧
    ∃ z : Fin n → ℤ, ∀ j,
      (1:ℝ)/(k+1) < |((fun i => (z i : ℝ)) ᵥ* g.1) j| ∧
      |((fun i => (z i : ℝ)) ᵥ* g.1) j| < k+1}

open scoped Matrix
open Matrix

open TopologicalSpace
open scoped Topology

lemma continuous_integer_row (n : ℕ) (z : Fin n → ℤ) :
    Continuous (fun g : G n => (fun i => (z i : ℝ)) ᵥ* g.1) := by
  apply continuous_pi
  intro j
  change Continuous (fun g : G n => ∑ i, (z i : ℝ)*g.1 i j)
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul
    ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)))

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_CyclicInduction
attribute [-instance] _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cyclic subgroup coefficients for Stark descent

Möbius inversion on the finite poset of cyclic subgroups expresses the
constant function as an integer combination of their indicators.
Averaging conjugates gives the denominator-cleared cyclic permutation
identity used to compare Dedekind zeta orders.
-/

open scoped BigOperators Classical

namespace DukePrimeDegree

noncomputable instance instFintypeCyclicSubgroups (G : Type*) [Group G] [Finite G] :
    Fintype (CyclicSubgroups G) := Fintype.ofFinite _

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealNorms
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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
namespace PrimeDegreePackets



def OrdinaryBallBound (n : ℕ) (μ : Measure (X n)) : Prop :=
  ∀ Ω : Set (X n), IsCompact Ω → ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧
    ∀ x ∈ Ω, ∀ r : ℝ, 0 < r → r < r₀ →
      μ ((fun h => rightAction x h) '' matrixBall n r) ≤ ENNReal.ofReal (C*r^n)

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ObservationCovers
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk
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



lemma diagonalOneParameter_nat {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (k : ℕ) : diagonalOneParameter ell hell (k:ℝ) = (diagonalOneParameter ell hell 1)^k := by
  induction k with
  | zero => simp [diagonalOneParameter_zero]
  | succ k ih => rw [Nat.cast_add,Nat.cast_one,diagonalOneParameter_add,ih,pow_succ]



end PrimeDegreePackets


namespace PrimeDegreePackets

lemma rightAction_iterate {n : ℕ} (a : G n) (k : ℕ) (x : X n) :
    (fun y => rightAction y a)^[k] x = rightAction x (a^k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply',ih,rightAction_mul,pow_succ]

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_AtomMass
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

lemma diagonalOneParameter_eq_diagonalFlow {d : ℕ} (ell : Fin (d+1) → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) :
    diagonalOneParameter ell hell t = diagonalFlow (fun i : Fin d => ell i.castSucc*t) := by
  apply Subtype.ext
  change Matrix.diagonal _ = Matrix.diagonal _
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    congr 1
    rw [← Finset.sum_mul]
    have H := hell
    rw [Fin.sum_univ_castSucc] at H
    have H' : ell (Fin.last d) = -∑ j : Fin d, ell j.castSucc := by linarith
    rw [H']
    ring
  · simp only [Fin.snoc_castSucc]



end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootSubgroups
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk
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


namespace PrimeDegreePackets

 
def invariantRightSubgroup {n : ℕ} (μ : Measure (X n)) : Subgroup (G n) where
  carrier := {g | Measure.map (fun x => rightAction x g) μ = μ}
  one_mem' := by
    change Measure.map (fun x : X n => rightAction x 1) μ = μ
    rw [show (fun x : X n => rightAction x 1) = id from funext rightAction_one]
    exact Measure.map_id
  mul_mem' {g h} hg hh := by
    change Measure.map (fun x => rightAction x (g*h)) μ = μ
    have heq : (fun x : X n => rightAction x (g*h)) =
        ((fun x => rightAction x h) ∘ (fun x => rightAction x g)) := by
      funext x
      exact (rightAction_mul x g h).symm
    rw [heq,←Measure.map_map (continuous_rightAction h).measurable
      (continuous_rightAction g).measurable,hg,hh]
  inv_mem' {g} hg := by
    change Measure.map (fun x => rightAction x g⁻¹) μ = μ
    calc
      _ = Measure.map (fun x => rightAction x g⁻¹)
        (Measure.map (fun x => rightAction x g) μ) := by rw [hg]
      _ = μ := by
        rw [Measure.map_map (continuous_rightAction g⁻¹).measurable
          (continuous_rightAction g).measurable]
        have heq : (fun x : X n => rightAction (rightAction x g) g⁻¹) = id := by
          funext x
          simp
        rw [show ((fun x : X n => rightAction x g⁻¹) ∘
          (fun x => rightAction x g)) = id from heq,Measure.map_id]



end PrimeDegreePackets

open scoped Topology Classical Matrix
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaDerivatives
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
namespace PrimeDegreePackets

lemma coordinateContraction_vector (d : ℕ) (j : Fin (d+1))
    (v : Fin (d+1) → ℝ) (hv : v j = 0) (t : ℝ) :
    diagonalLinear (d+1) (fun i => Real.exp (coordinateContractionWeights d j i*t)) v =
      Real.exp (-t) • v := by
  ext i
  by_cases hi : i=j
  · subst i; simp [diagonalLinear,hv]
  · simp [diagonalLinear,coordinateContractionWeights,hi]



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootRelations
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

lemma vecMul_mem_pointLattice_rightAction {n : ℕ} (x : X n) (h : G n)
    (v : Fin n → ℝ) (hv : v ∈ pointLattice x) :
    v ᵥ* h.1 ∈ pointLattice (rightAction x h) := by
  induction x using Quotient.inductionOn with
  | h g =>
    rw [pointLattice_mk,← integerRowMap_range] at hv
    obtain ⟨z,rfl⟩ := hv
    change integerRowMap g.1 z ᵥ* h.1 ∈ rowLattice (g*h).1
    rw [←integerRowMap_range]
    refine ⟨z,?_⟩
    simp only [integerRowMap_apply,Matrix.SpecialLinearGroup.coe_mul,Matrix.vecMul_vecMul]


lemma root_stabilizer_trivial_of_no_coordinate_zero {n : ℕ} (x : X n)
    (hx : ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0)
    (i j : Fin n) (hij : i ≠ j) (a : ℝ)
    (ha : rightAction x (Matrix.SpecialLinearGroup.transvection hij a) = x) :
    a = 0 := by
  by_contra hane
  have hex : ∃ v ∈ pointLattice x, v i ≠ 0 := by
    induction x using Quotient.inductionOn with
    | h g =>
      obtain ⟨z,hz⟩ := exists_integer_row_no_zero_coordinate g
      refine ⟨integerRowMap g.1 z,?_,?_⟩
      · rw [pointLattice_mk,←integerRowMap_range]
        exact ⟨z,rfl⟩
      · simpa only [integerRowMap_apply] using hz i
  obtain ⟨v,hv,hvi⟩ := hex
  let w := v ᵥ* Matrix.transvection i j a - v
  have hw : w ∈ pointLattice x := by
    apply Submodule.sub_mem _ _ hv
    have H := vecMul_mem_pointLattice_rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a) v hv
    simpa only [ha,Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection] using H
  have hwj : w j = v i*a := by simp [w,vecMul_transvection_apply]
  have hw0 : w ≠ 0 := by
    intro H
    exact mul_ne_zero hvi hane (hwj.symm.trans (congrFun H j))
  apply hx w hw hw0 i
  simp [w,vecMul_transvection_apply,hij.symm]



end PrimeDegreePackets


open scoped Topology Classical ENNReal

open scoped Matrix Topology Classical
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootCharts
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

lemma mul_diagonalOneParameter_entry {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (g : G n) (r s : Fin n) (t : ℝ) :
    (g * diagonalOneParameter ell hell t).1 r s = g.1 r s * Real.exp (ell s*t) := by
  exact Matrix.mul_diagonal _ _ _ _

 
def rootSliceDiagonal {n : ℕ} {i j k : Fin n} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) (s : RootSlice i j k) : RootSlice i j k :=
  ⟨s.val * diagonalOneParameter ell hell t, by
    constructor
    · rw [mul_diagonalOneParameter_entry]
      exact mul_ne_zero s.prop.1 (Real.exp_ne_zero _)
    · rw [mul_diagonalOneParameter_entry,s.prop.2,zero_mul]⟩

lemma rootSliceDiagonal_add {n : ℕ} {i j k : Fin n} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t u : ℝ) (s : RootSlice i j k) :
    rootSliceDiagonal ell hell (t+u) s =
      rootSliceDiagonal ell hell u (rootSliceDiagonal ell hell t s) := by
  apply Subtype.ext
  exact congrArg (s.val * ·) (diagonalOneParameter_add ell hell t u) |>.trans (mul_assoc _ _ _).symm

lemma rootSliceDiagonal_zero {n : ℕ} {i j k : Fin n} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (s : RootSlice i j k) :
    rootSliceDiagonal ell hell 0 s = s := by
  apply Subtype.ext
  simp only [rootSliceDiagonal,diagonalOneParameter_zero,mul_one]

def rootSliceDiagonalHomeomorph {n : ℕ} {i j k : Fin n} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) : RootSlice i j k ≃ₜ RootSlice i j k where
  toFun := rootSliceDiagonal ell hell t
  invFun := rootSliceDiagonal ell hell (-t)
  left_inv s := by rw [← rootSliceDiagonal_add,add_neg_cancel,rootSliceDiagonal_zero]
  right_inv s := by rw [← rootSliceDiagonal_add,neg_add_cancel,rootSliceDiagonal_zero]
  continuous_toFun := (continuous_subtype_val.mul continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.mul continuous_const).subtype_mk _



theorem root_conditional_scaling {n : ℕ} {i j k : Fin n}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (ρ : Measure (RootSlice i j k × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ s ∂ρ.fst,
      (ρ.map (Prod.map (rootSliceDiagonalHomeomorph ell hell t)
        (rootTimeScaling ell i j t))).condKernel (rootSliceDiagonal ell hell t s) =
        (ρ.condKernel s).map (rootTimeScaling ell i j t) := by
  exact condKernel_map_measurableEquiv ρ
    (rootSliceDiagonalHomeomorph ell hell t).toMeasurableEquiv
    (rootTimeScaling ell i j t).toMeasurableEquiv

end PrimeDegreePackets


namespace PrimeDegreePackets

abbrev rootDiagonalCoordinates {n : ℕ} {i j k : Fin n} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) :
    (RootSlice i j k × ℝ) ≃ₜ (RootSlice i j k × ℝ) :=
  (rootSliceDiagonalHomeomorph ell hell t).prodCongr (rootTimeScaling ell i j t)

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_KernelScaling
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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
namespace PrimeDegreePackets.RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}



def timeTranslation (a : ℝ) : (RootSlice i j k × ℝ) ≃ₜ (RootSlice i j k × ℝ) :=
  (Homeomorph.refl _).prodCongr (Homeomorph.addRight a)

end PrimeDegreePackets.RootBox
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_XiBoundary
attribute [-instance] _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

omit [Fintype d] in
lemma torusProjection_eq_iff (x y : d → ℝ) :
    torusProjection x = torusProjection y ↔ ∃ z : d → ℤ, y = x + integerVector z := by
  constructor
  · intro h
    have H (i : d) : ∃ z : ℤ, (z:ℝ) = -(x i) + y i := by
      have hi := QuotientAddGroup.eq.mp (congrFun h i)
      simpa only [AddSubgroup.mem_zmultiples_iff,zsmul_eq_mul,mul_one] using hi
    choose z hz using H
    exact ⟨z,funext (fun i => by dsimp [integerVector] <;> linarith [hz i])⟩
  · rintro ⟨z,rfl⟩
    funext i
    apply QuotientAddGroup.eq.mpr
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨z i,?_⟩
    simp [integerVector,zsmul_eq_mul]

def translate (f : C(d → ℝ,ℂ)) (z : d → ℤ) : C(d → ℝ,ℂ) :=
  f.comp (ContinuousMap.addRight (integerVector z))

def LocallyNormal (f : C(d → ℝ,ℂ)) : Prop :=
  ∀ K : TopologicalSpace.Compacts (d → ℝ),
    Summable (fun z : d → ℤ => ‖(translate f z).restrict K‖)

def periodizedReal (f : C(d → ℝ,ℂ)) : C(d → ℝ,ℂ) := ∑' z : d → ℤ, translate f z

lemma periodizedReal_apply (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f) (x : d → ℝ) :
    periodizedReal f x = ∑' z : d → ℤ, f (x + integerVector z) := by
  exact (ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm hf) x).symm

lemma periodizedReal_per (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f)
    (x : d → ℝ) (z : d → ℤ) :
    periodizedReal f (x + integerVector z) = periodizedReal f x := by
  rw [periodizedReal_apply f hf,periodizedReal_apply f hf]
  convert (Equiv.addLeft z).tsum_eq (fun n : d → ℤ => f (x + integerVector n)) using 1
  all_goals try with_reducible_and_instances rfl
  apply tsum_congr
  intro n
  congr 1
  ext i
  simp [integerVector,add_assoc]

lemma periodizedReal_representative (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f) (x : d → ℝ) :
    periodizedReal f (torusRepresentative (torusProjection x)) = periodizedReal f x := by
  obtain ⟨z,hz⟩ := (torusProjection_eq_iff x (torusRepresentative (torusProjection x))).mp
    (torusProjection_representative _).symm
  rw [hz]
  exact periodizedReal_per f hf x z

def periodizedTorus (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f) : C(UnitAddTorus d,ℂ) where
  toFun y := periodizedReal f (torusRepresentative y)
  continuous_toFun := by
    apply torusProjection_openQuotient.isQuotientMap.continuous_iff.mpr
    have he : (fun y => periodizedReal f (torusRepresentative y)) ∘ torusProjection =
        periodizedReal f := funext (periodizedReal_representative f hf)
    rw [he]
    exact (periodizedReal f).continuous

instance integerTranslationAction : AddAction (d → ℤ) (d → ℝ) where
  vadd z x := integerVector z + x
  zero_vadd x := by
    change integerVector 0 + x = x
    ext i
    simp [integerVector]
  add_vadd z w x := by
    change integerVector (z+w) + x = integerVector z + (integerVector w + x)
    ext i
    simp [integerVector,add_assoc]

instance integerTranslationMeasurable : MeasurableConstVAdd (d → ℤ) (d → ℝ) :=
  ⟨fun _ => measurable_const.add measurable_id⟩

instance integerTranslationPreservesVolume :
    VAddInvariantMeasure (d → ℤ) (d → ℝ) volume where
  measure_preimage_vadd z S hS := by
    exact (measurePreserving_add_left volume (integerVector z)).measure_preimage hS.nullMeasurableSet

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CoordinateLattices
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem
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

lemma integerVector_mem (z : d → ℤ) : integerVector z ∈ coordinateLattice := by
  apply ((Pi.basisFun ℝ d).mem_span_iff_repr_mem ℤ _).mpr
  intro i
  exact ⟨z i, by simp [integerVector]⟩

def integerVectorInLattice (z : d → ℤ) : coordinateLattice (d := d) :=
  ⟨integerVector z,integerVector_mem z⟩

end PrimeDegreePackets.ThetaConstruction

open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty

open scoped FourierTransform

open scoped BigOperators SchwartzMap FourierTransform

open scoped BigOperators FourierTransform
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]



def latticeTheta (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (b : ℝ) : ℂ :=
  ∑' z : d → ℤ, Complex.exp (-(b:ℂ) * ‖B (euclideanInteger z)‖^2)

end PrimeDegreePackets.ThetaConstruction

open MeasureTheory Set Filter Topology Module WithLp Asymptotics
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LatticeTheta
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

def normalizedTheta (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (t : ℝ) : ℂ :=
  latticeTheta B (Real.pi*t)

def thetaMellinContinuation (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (s : ℂ) : ℂ :=
  mellin (normalizedThetaTail B) s + ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
    mellin (normalizedThetaTail (adjointEquiv B.symm)) ((Fintype.card d:ℂ)/2-s) +
      ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) / (s-(Fintype.card d:ℂ)/2) - 1/s



end PrimeDegreePackets.ThetaConstruction

open Module MeasureTheory


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

def latticeEnergy (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (z : NonzeroIntegerVector d) : ℝ := Real.pi * ‖B (euclideanInteger z.1)‖^2

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ThetaTails
attribute [-instance] _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
variable (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)


def averagedNormalizedThetaTail (t : ℝ) : ℂ := ∫ x, normalizedThetaTail (B x) t ∂μ

end PrimeDegreePackets.ThetaConstruction


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZeroReflection
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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


namespace PrimeDegreePackets.HeckeMellin


def logEnergy {d : ℕ} (a : Fin (d+1) → ℝ) (u : LogCoordinates d) : ℝ :=
  ∑ i, (a i * Real.exp (restoredLogCoordinates u i))^2


def logRadialKernel {d : ℕ} (s : ℂ) (r : ℝ) (a : Fin (d+1) → ℝ)
    (p : ℝ × LogCoordinates d) : ℂ :=
  Complex.exp (((d+1 : ℕ) : ℂ)*s/2*(p.1 : ℂ) - (r*Real.exp p.1*logEnergy a p.2 : ℝ))


def radialKernel {d : ℕ} (s : ℂ) (r : ℝ) (a : Fin (d+1) → ℝ)
    (t : ℝ) (u : LogCoordinates d) : ℂ :=
  (t : ℂ)^(((d+1 : ℕ) : ℂ)*s/2-1) *
    Complex.exp (-(r*t*logEnergy a u : ℝ))

end PrimeDegreePackets.HeckeMellin
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RadialIntegrals
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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


namespace PrimeDegreePackets.HeckeMellin

 
def realRadialKernel {d : ℕ} (s r : ℝ) (a : Fin (d+1) → ℝ)
    (t : ℝ) (u : LogCoordinates d) : ℝ :=
  t^((d+1 : ℝ)*s/2-1) * Real.exp (-r*t*logEnergy a u)

end PrimeDegreePackets.HeckeMellin

open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction



def nonnegativeIdealThetaMellin {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (S : Set (LogCoordinates d)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi 0, ENNReal.ofReal (t^((d+1 : ℝ)*s/2-1)) *
    ∫⁻ u in S, ENNReal.ofReal ((normalizedTheta
      (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
        (restoredLogCoordinates u)) t-1).re)

end PrimeDegreePackets.HeckeMellin

open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction


def idealThetaMellinKernel {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) (p : ℝ × LogCoordinates d) : ℂ :=
  (p.1 : ℂ)^(((d+1 : ℕ) : ℂ)*s/2-1) *
    (normalizedTheta
      (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
        (restoredLogCoordinates p.2)) p.1-1)

end PrimeDegreePackets.HeckeMellin
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealThetaXi
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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
namespace PrimeDegreePackets.HeckeMellin

 

def regularizedThetaZeta {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (s : ℂ) : ℂ :=
  completedThetaXi σ hn s *
    (completionExponential (d+1) |(NumberField.discr K : ℝ)| s)⁻¹ *
    ((Complex.Gamma (s/2))⁻¹)^(d+1) / s

end PrimeDegreePackets.HeckeMellin

open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ThetaReflection
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

 
def idealThetaXiOn {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (S : Set (LogCoordinates d)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  ∫ u in S, thetaMellinXi (logScaledLattice
    (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
    (restoredLogCoordinates u)) (((d+1 : ℕ) : ℂ)*s/2)

end PrimeDegreePackets.HeckeMellin


open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
namespace PrimeDegreePackets.HeckeMellin



def dedekindXiZeros {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) : Set ℂ := {s | completedThetaXi σ hn s = 0}

end PrimeDegreePackets.HeckeMellin
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_NormalClosure
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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


def idealClassThetaXi {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (w : ClassGroup (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∑ c : ClassGroup (𝓞 K), w c⁻¹ *
    (((FractionalIdeal.absNorm (classRepresentative K c).val : ℝ) : ℂ)^s *
      idealThetaXi σ hn (classRepresentative K c) s)

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

 
def completedIdealClassXi {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (w : ClassGroup (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ((2 : ℂ)^(d+1)/((d+1 : ℕ) : ℂ)) *
    Complex.exp (s*(Real.log |(NumberField.discr K : ℝ)| : ℂ)/2) *
      idealClassThetaXi σ hn w s

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin



def entireIdealClassL {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (w : ClassGroup (𝓞 K) → ℂ) : ℂ → ℂ :=
  dslope (dslope (completedIdealClassXi σ hn w) 0) 1

end PrimeDegreePackets.HeckeMellin
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealClasses
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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


namespace PrimeDegreePackets.HeckeMellin

 

def idealClassLFunction {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (χ : ClassGroup (𝓞 K) →* ℂ) (s : ℂ) : ℂ :=
  (completionExponential (d+1) |(NumberField.discr K : ℝ)| s)⁻¹ *
    (Complex.Gamma (s/2))⁻¹ ^ (d+1) * entireIdealClassL σ hn χ s

end PrimeDegreePackets.HeckeMellin

open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate

open Module


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 
def cosetLatticeTheta (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : d → ℝ) (b : ℝ) : ℂ :=
  ∑' z : d → ℤ, Complex.exp (-(b:ℂ) *
    ‖B (toLp 2 x + euclideanInteger z)‖^2)



def congruenceTheta {I : Type*} [Fintype I]
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : I → d → ℝ) (w : I → ℂ) (b : ℝ) : ℂ :=
  ∑ i, w i * cosetLatticeTheta B (x i) b


end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CongruenceLattices
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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



attribute [local instance] OAI.PrimeDegreePackets.ThetaConstruction.congruenceLatticesDecidableEq
def periodicLatticeTheta (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (b : ℝ) : ℂ :=
  ∑' z : d → ℤ, w ((integerCongruenceEquiv N z).1) *
    Complex.exp (-(b:ℂ) * ‖B ((N:ℝ)⁻¹ • euclideanInteger z)‖^2)

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]


def weightedThetaRemainder
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (t : ℝ) : ℂ :=
  ∑' z : NonzeroIntegerVector d,
    a z.1 * Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z.1)‖^2)

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 
def scaledWeightedThetaTail (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (k : ℝ) : ℝ → ℂ :=
  (Set.Ioi 1).indicator (fun t => weightedThetaRemainder B a (k * max t 1))

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PeriodicTheta
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

attribute [local instance] OAI.PrimeDegreePackets.ThetaConstruction.periodicThetaDecidableEq
def normalizedPeriodicTheta (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) (t : ℝ) : ℂ :=
  periodicLatticeTheta B N w (Real.pi*t)

def periodicPrimalTail (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) [NeZero N] (w : (d → Fin N) → ℂ) : ℝ → ℂ :=
  scaledWeightedThetaTail B (periodicPrimalWeight N w) (Real.pi/(N:ℝ)^2)

def periodicDualTail (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (N : ℕ) (w : (d → Fin N) → ℂ) : ℝ → ℂ :=
  scaledWeightedThetaTail (adjointEquiv B.symm) (periodicDualWeight N w) Real.pi

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d R : Type*} [Fintype d] [CommRing R]

local instance rationalModulusDecidableEq_r73f8bb_1 : DecidableEq d := Classical.decEq d
lemma rationalModulusIdeal_restrictScalars (N : ℕ) :
    (rationalModulusIdeal R N).restrictScalars ℤ =
      LinearMap.range (LinearMap.lsmul ℤ R N) := by
  ext x
  change x ∈ Ideal.span {(N : R)} ↔ _
  simp only [Ideal.mem_span_singleton, dvd_def, LinearMap.mem_range,
    LinearMap.lsmul_apply, zsmul_eq_mul, Int.cast_natCast, eq_comm]

 

def rationalModulusEquivModN (N : ℕ) : (R ⧸ rationalModulusIdeal R N) ≃+ ModN R N :=
  (Submodule.quotEquivOfEq _ _ (rationalModulusIdeal_restrictScalars (R := R) N)).toAddEquiv

 
def integralResidueEquiv (b : Basis d ℤ R) (N : ℕ) [NeZero N] :
    (d → Fin N) ≃ (R ⧸ rationalModulusIdeal R N) :=
  ((Equiv.piCongrRight fun _ : d => (ZMod.finEquiv N).toEquiv).trans
    (ModN.basis b).equivFun.symm.toEquiv).trans (rationalModulusEquivModN N).symm.toEquiv

end PrimeDegreePackets.ThetaConstruction

open MeasureTheory Module
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntegerEmbeddings
attribute [-instance] _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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


namespace PrimeDegreePackets
open ThetaConstruction
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]

def subgroupUnitLogOnto (σ : OrderedEmbeddings (d+1) K) (S : Subgroup (𝓞 K)ˣ) :
    Additive S →+ orderedLogSubgroup σ S where
  toFun z := ⟨orderedUnitLog σ (Additive.ofMul z.toMul.val),
    (mem_orderedLogSubgroup σ S _).mpr ⟨z.toMul.val,z.toMul.property,rfl⟩⟩
  map_zero' := Subtype.ext ((orderedUnitLog σ).map_zero)
  map_add' _ _ := Subtype.ext ((orderedUnitLog σ).map_add _ _)

end PrimeDegreePackets


namespace PrimeDegreePackets.ThetaConstruction
variable {d R : Type*} [Fintype d] [CommRing R]

attribute [local instance] OAI.PrimeDegreePackets.ThetaConstruction.integerEmbeddingsDecidableEq
lemma rationalModulus_nsmul (N : ℕ) (x : R ⧸ rationalModulusIdeal R N) :
    N • x = 0 := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_nsmul,Ideal.Quotient.eq_zero_iff_mem]
  change N • x ∈ Ideal.span {(N:R)}
  rw [nsmul_eq_mul,Ideal.mem_span_singleton]
  exact dvd_mul_right _ _

def idealModNReduction (I : Ideal R) (N : ℕ) :
    ModN I N →+ R ⧸ rationalModulusIdeal R N :=
  ModN.liftEquiv.symm ⟨(Ideal.Quotient.mk (rationalModulusIdeal R N)).toAddMonoidHom.comp
    I.subtype.toAddMonoidHom, fun _ => rationalModulus_nsmul N _⟩

lemma idealModNReduction_mk (I : Ideal R) (N : ℕ) (x : I) :
    idealModNReduction I N (ModN.mkQ N x) =
      Ideal.Quotient.mk (rationalModulusIdeal R N) x := rfl

lemma idealModNReduction_surjective (I : Ideal R) (N : ℕ)
    (hI : IsCoprime I (rationalModulusIdeal R N)) :
    Function.Surjective (idealModNReduction I N) := by
  obtain ⟨a,ha,b,hb,hab⟩ := Ideal.isCoprime_iff_exists.mp hI
  intro y
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨ModN.mkQ N ⟨a*y,I.mul_mem_right y ha⟩, ?_⟩
  rw [idealModNReduction_mk,map_mul]
  have Ha : Ideal.Quotient.mk (rationalModulusIdeal R N) a = 1 := by
    have H := congrArg (Ideal.Quotient.mk (rationalModulusIdeal R N)) hab
    rw [map_add,Ideal.Quotient.eq_zero_iff_mem.mpr hb,add_zero,map_one] at H
    exact H
  rw [Ha,one_mul]

lemma idealModNReduction_bijective (I : Ideal R) (bI : Basis d ℤ I) (bR : Basis d ℤ R)
    (N : ℕ) [NeZero N] (hI : IsCoprime I (rationalModulusIdeal R N)) :
    Function.Bijective (idealModNReduction I N) := by
  let : Fintype (ModN I N) := Fintype.ofEquiv (d → Fin N) (moduleResidueEquiv bI N)
  let : Fintype (R ⧸ rationalModulusIdeal R N) :=
    Fintype.ofEquiv (d → Fin N) (integralResidueEquiv bR N)
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨idealModNReduction_surjective I N hI,?_⟩
  exact (Fintype.card_congr (moduleResidueEquiv bI N)).symm.trans
    (Fintype.card_congr (integralResidueEquiv bR N))

def idealResidueEquiv (I : Ideal R) (bI : Basis d ℤ I) (bR : Basis d ℤ R)
    (N : ℕ) [NeZero N] (hI : IsCoprime I (rationalModulusIdeal R N)) :
    (d → Fin N) ≃ R ⧸ rationalModulusIdeal R N :=
  (moduleResidueEquiv bI N).trans (Equiv.ofBijective (idealModNReduction I N)
    (idealModNReduction_bijective I bI bR N hI))

def idealCharacterWeight (I : Ideal R) (bI : Basis d ℤ I) (N : ℕ) [NeZero N]
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) : (d → Fin N) → ℂ :=
  fun r => χ (idealModNReduction I N (moduleResidueEquiv bI N r))

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
variable (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (k : ℝ)

def averagedWeightedThetaTail (t : ℝ) : ℂ := ∫ x, scaledWeightedThetaTail (B x) a k t ∂μ

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_GaussianMellin
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

attribute [local instance] OAI.PrimeDegreePackets.ThetaConstruction.averagedPeriodicThetaDecidableEq
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)

def averagedNormalizedPeriodicTheta (N : ℕ) [NeZero N]
    (w : (d → Fin N) → ℂ) (t : ℝ) : ℂ := ∫ x, normalizedPeriodicTheta (B x) N w t ∂μ



end PrimeDegreePackets.ThetaConstruction


open MeasureTheory Module WithLp Set
namespace PrimeDegreePackets.ThetaConstruction
variable {d R : Type*} [Fintype d] [CommRing R]


local instance gaussianMellinDecidableEq_r73f8bb_1 : DecidableEq d := Classical.decEq d
def idealCharacterTheta (I : Ideal R) (bI : Basis d ℤ I)
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (N : ℕ)
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (t : ℝ) : ℂ :=
  ∑' a : I, χ (Ideal.Quotient.mk (rationalModulusIdeal R N) (a:R)) *
    Complex.exp (-((Real.pi*t : ℝ):ℂ)*‖B (euclideanInteger (bI.equivFun a))‖^2)

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets
open ThetaConstruction
variable {n : ℕ} {K : Type*} [Field K] [NumberField K]



def idealResidueFlowTheta {d : ℕ} (σ : OrderedEmbeddings (d+1) K)
    (I : Ideal (𝓞 K)) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (u : LogCoordinates d) (t : ℝ) : ℂ :=
  ∑' a : I, χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (a:𝓞 K)) *
    Complex.exp (-((Real.pi*t : ℝ):ℂ) *
      ‖toLp 2 (fun j => logFlowWeights u j * σ j ((a:𝓞 K):K))‖^2)

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealThetaFlow
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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


namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
variable {K : Type*} [Field K] [NumberField K]

 
def idealIntegerElement (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) : 𝓞 K :=
  ((FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp a.property).choose

lemma idealIntegerElement_coe (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) :
    (idealIntegerElement I hI a : K) = (a.val:K) :=
  ((FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp a.property).choose_spec.2

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_UnitOrbitIntegrals
attribute [-instance] _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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
open HeckeMellin ThetaConstruction
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]

def residueIdealMellinFactor (σ : OrderedEmbeddings (d+1) K) : ℂ :=
  (Nat.card (subgroupUnitLogOnto σ ⊤).ker : ℂ) *
    (2/(d+1:ℂ)) * (1/2:ℂ)^(d+1)



def residueIdealContinued (σ : OrderedEmbeddings (d+1) K)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (s : ℂ) : ℂ :=
  (residueIdealMellinFactor σ)⁻¹ * ((Complex.Gammaℝ s)⁻¹)^(d+1) *
    ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val:ℝ):ℂ)^s *
      mellin (fun t => ∫ u in orderedThetaLogDomain σ, idealResidueFlowTheta σ I N χ u t)
        (((d+1:ℕ):ℂ)*s/2)


end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayCharacter
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem
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



variable {K : Type*} [Field K] [NumberField K]



namespace EvenRayCharacter
variable {N : ℕ} (ψ : EvenRayCharacter K N)



def underlyingIdeal (J : integralFractionalIdeals K) : Ideal (𝓞 K) :=
  ((integralFractionalIdealsEquiv K).symm J).val

lemma underlyingIdeal_ne_bot (J : integralFractionalIdeals K) :
    underlyingIdeal J ≠ ⊥ := ((integralFractionalIdealsEquiv K).symm J).property

lemma underlyingIdeal_coe (J : integralFractionalIdeals K) :
    (underlyingIdeal J : FractionalIdeal (𝓞 K)⁰ K) = J.val.val := by
  have H := (integralFractionalIdealsEquiv K).apply_symm_apply J
  exact congrArg (fun U : integralFractionalIdeals K => U.val.val) H



lemma generator_principal_product (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    Ideal.span {idealIntegerElement I hI (idealElementRepresentative _ J)} =
      I * underlyingIdeal ⟨J.val, J.property.1⟩ := by
  let U := integralIdealFractionalUnit I hI
  have h := congrArg Subtype.val (idealElementRepresentative_spec U J)
  change relativeElementIdeal U (idealElementRepresentative U J).val = J.val at h
  have hm : J.val * U = toPrincipalIdeal (𝓞 K) K (idealElementRepresentative U J).val := by
    rw [← h]
    simp [relativeElementIdeal]
  apply FractionalIdeal.coeIdeal_injective (K := K)
  change (Ideal.span {idealIntegerElement I hI (idealElementRepresentative U J)} :
    FractionalIdeal (𝓞 K)⁰ K) = ((I * underlyingIdeal ⟨J.val, J.property.1⟩ : Ideal (𝓞 K)) :
      FractionalIdeal (𝓞 K)⁰ K)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  have he : algebraMap (𝓞 K) K
      (idealIntegerElement I hI (idealElementRepresentative U J)) =
      ((idealElementRepresentative U J).val : K) := idealIntegerElement_coe I hI _
  rw [he]
  have H := congrArg (fun W : (FractionalIdeal (𝓞 K)⁰ K)ˣ => W.val) hm
  simp only [Units.val_mul, coe_toPrincipalIdeal] at H
  exact H.symm.trans (by erw [underlyingIdeal_coe]; exact mul_comm _ _)

lemma generator_integer_ne_zero (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    idealIntegerElement I hI (idealElementRepresentative _ J) ≠ 0 := by
  intro hz
  have H := idealIntegerElement_coe I hI (idealElementRepresentative _ J)
  rw [hz] at H
  change (0 : K) = _ at H
  exact (idealElementRepresentative _ J).val.ne_zero H.symm

lemma generator_fractional_product (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    integralIdealFractionalUnit
      (Ideal.span {idealIntegerElement I hI (idealElementRepresentative _ J)})
      (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using
        generator_integer_ne_zero I hI J) = integralIdealFractionalUnit I hI * J.val := by
  apply Units.ext
  change (Ideal.span {idealIntegerElement I hI (idealElementRepresentative _ J)} :
    FractionalIdeal (𝓞 K)⁰ K) = _
  erw [generator_principal_product, FractionalIdeal.coeIdeal_mul, underlyingIdeal_coe]
  rfl

 

def coefficient (J : integralFractionalIdeals K) : ℂ :=
  if IsCoprime (underlyingIdeal J) (rationalModulusIdeal (𝓞 K) N)
  then (ψ.idealHom J.val : ℂ) else 0


def dirichlet (s : ℂ) : ℂ :=
  ∑' J : integralFractionalIdeals K,
    ψ.coefficient J * ((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)^(-s)



def classIdeal (K : Type*) [Field K] [NumberField K] (N : ℕ) [NeZero N]
    (c : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  coprimeClassRepresentative (rationalModulusIdeal (𝓞 K) N)
    (by simp [rationalModulusIdeal, NeZero.ne N]) c

lemma classIdeal_ne_bot [NeZero N] (c : ClassGroup (𝓞 K)) :
    (classIdeal K N c).val ≠ ⊥ :=
  mem_nonZeroDivisors_iff_ne_zero.mp (classIdeal K N c).property

lemma classIdeal_coprime [NeZero N] (c : ClassGroup (𝓞 K)) :
    IsCoprime (classIdeal K N c).val (rationalModulusIdeal (𝓞 K) N) :=
  (coprimeClassRepresentative_spec _ _ c).1

lemma classIdeal_class [NeZero N] (c : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (integralIdealFractionalUnit (classIdeal K N c).val
      (classIdeal_ne_bot c)) = c := by
  change ClassGroup.mk K (FractionalIdeal.mk0 K (classIdeal K N c)) = c
  rw [ClassGroup.mk_mk0]
  exact (coprimeClassRepresentative_spec _ _ c).2

 

def classPartition [NeZero N] :
    (Σ c : ClassGroup (𝓞 K), integralIdealClassFiber
      (integralIdealFractionalUnit (classIdeal K N c).val (classIdeal_ne_bot c))) ≃
        integralFractionalIdeals K where
  toFun x := ⟨x.2.1, x.2.2.1⟩
  invFun J := ⟨(ClassGroup.mk K J.1)⁻¹,
    ⟨J.1, J.2, by rw [classIdeal_class, inv_inv]⟩⟩
  left_inv := by
    rintro ⟨c, J⟩
    have h : (ClassGroup.mk K J.1)⁻¹ = c := by
      rw [J.2.2, classIdeal_class, inv_inv]
    apply Sigma.ext h
    exact (Subtype.heq_iff_coe_eq (fun x => by
      change (x.val ≤ 1 ∧ ClassGroup.mk K x =
        (ClassGroup.mk K (integralIdealFractionalUnit
          (classIdeal K N ((ClassGroup.mk K J.val)⁻¹)).val
          (classIdeal_ne_bot _)))⁻¹) ↔ _
      rw [h])).mpr rfl
  right_inv _ := rfl

variable [NeZero N]

 

def continued {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (s : ℂ) : ℂ :=
  ∑ c : ClassGroup (𝓞 K),
    ((ψ.idealHom (integralIdealFractionalUnit
      (classIdeal K N c).val (classIdeal_ne_bot c)) : ℂ))⁻¹ *
        residueIdealContinued σ (classIdeal K N c).val (classIdeal_ne_bot c) N ψ.residue s



end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayEuler
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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
variable (ψ : EvenRayCharacter K N)


lemma integralUnit_mul (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    integralIdealFractionalUnit (I*J) (mul_ne_zero hI hJ) =
      integralIdealFractionalUnit I hI * integralIdealFractionalUnit J hJ := by
  apply Units.ext
  exact FractionalIdeal.coeIdeal_mul I J

end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayDescent
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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
variable (ψ : EvenRayCharacter K N)

lemma underlyingIdeal_integralUnit (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    underlyingIdeal ⟨integralIdealFractionalUnit J hJ, FractionalIdeal.coeIdeal_le_one⟩ = J := by
  apply FractionalIdeal.coeIdeal_injective (K := K)
  exact underlyingIdeal_coe ⟨integralIdealFractionalUnit J hJ,
    FractionalIdeal.coeIdeal_le_one⟩



end EvenRayCharacter

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ArtinSeries
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem
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

def artinCoefficient (χ : (E ≃ₐ[F] E) →* ℂˣ) (N : ℕ) (I : Ideal (𝓞 F)) : ℂ :=
  if hI : I ≠ ⊥ then
    if IsCoprime I (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) then
      (idealHom F E χ (integralIdealFractionalUnit I hI) : ℂ)
    else 0
  else 0

def artinDirichlet (χ : (E ≃ₐ[F] E) →* ℂˣ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' I : Ideal (𝓞 F), artinCoefficient F E χ N I * (Ideal.absNorm I : ℂ)^(-s)

namespace ArtinSeries
variable {F E} (χ : (E ≃ₐ[F] E) →* ℂˣ) (N : ℕ)

abbrev allCoefficient := artinCoefficient F E χ N

@[simp] lemma allCoefficient_bot : allCoefficient χ N ⊥ = 0 := by
  simp [allCoefficient, artinCoefficient]
@[simp] lemma allCoefficient_zero : allCoefficient χ N 0 = 0 := allCoefficient_bot χ N
@[simp] lemma allCoefficient_one : allCoefficient χ N 1 = 1 := by
  have hc : IsCoprime (⊤ : Ideal (𝓞 F)) (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) :=
    by rw [← Ideal.one_eq_top]; exact isCoprime_one_left
  have ht : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := top_ne_bot
  simp only [Ideal.one_eq_top, allCoefficient, artinCoefficient, dite_eq_left ht, hc,
    ite_true, if_true, integralIdealFractionalUnit_top, map_one, Units.val_one]

lemma allCoefficient_mul (I J : Ideal (𝓞 F)) :
    allCoefficient χ N (I*J) = allCoefficient χ N I * allCoefficient χ N J := by
  by_cases hI : I = 0
  · simp [hI]
  by_cases hJ : J = 0
  · simp [hJ]
  change I ≠ ⊥ at hI
  change J ≠ ⊥ at hJ
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  simp only [allCoefficient, artinCoefficient, dite_eq_left hI, dite_eq_left hJ, dite_eq_left hIJ,
    IsCoprime.mul_left_iff]
  by_cases hcI : IsCoprime I (ThetaConstruction.rationalModulusIdeal (𝓞 F) N)
  · by_cases hcJ : IsCoprime J (ThetaConstruction.rationalModulusIdeal (𝓞 F) N)
    · simp only [hcI, hcJ, and_self, ite_true, if_true]
      have H := congrArg (fun U : (FractionalIdeal (𝓞 F)⁰ F)ˣ =>
        (idealHom F E χ U : ℂ)) (EvenRayCharacter.integralUnit_mul I J hI hJ)
      simpa only [map_mul, Units.val_mul] using H
    · simp [hcI, hcJ]
  · simp [hcI]

def coefficientHom : Ideal (𝓞 F) →*₀ ℂ where
  toFun := allCoefficient χ N
  map_zero' := allCoefficient_zero χ N
  map_one' := allCoefficient_one χ N
  map_mul' := allCoefficient_mul χ N

def idealTerm {s : ℂ} (hs : 1 < s.re) : Ideal (𝓞 F) →*₀ ℂ :=
  coefficientHom χ N * (riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)).comp Ideal.absNorm

def normTerm {s : ℂ} (hs : 1 < s.re) (m : ℕ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = m}, idealTerm χ N hs I.val

end ArtinSeries
end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CosetMeromorphic
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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



def cosetRationalEuler (L : IntermediateField F E) (N : ℕ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  if p.val ∣ N then 1 else
    ∏ P : idealsOverPrime F p.val,
      (LinearMap.det (LinearMap.id - (Ideal.absNorm P.val : ℂ)^(-s) •
        (LinearEquiv.funCongrLeft ℂ ℂ
          (MulAction.toPerm (β := (E ≃ₐ[F] E) ⧸ L.fixingSubgroup)
            (primeFrobenius F E (rationalPrimeSpectrum F p P))⁻¹)).toLinearMap))⁻¹

open HeckeMellin
section ContinuedCoset
variable {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

 

def cosetMeromorphic (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (N : ℕ) (s : ℂ) : ℂ :=
  removedEulerPolynomial K N s * (regularizedThetaZeta σ hn s / (s-1))

end ContinuedCoset



end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayRealization
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module
open scoped NumberField nonZeroDivisors Classical
namespace PrimeDegreePackets.PrincipalRay
open ThetaConstruction
variable {F : Type*} [Field F] [NumberField F]
variable (φ : (FractionalIdeal (𝓞 F)⁰ F)ˣ →* ℂˣ)

def principalValue (a : 𝓞 F) (ha : a ≠ 0) : ℂˣ :=
  φ (integralIdealFractionalUnit (Ideal.span {a})
    (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha))

lemma principalValue_mul (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0) :
    principalValue φ (a*b) (mul_ne_zero ha hb) =
      principalValue φ a ha * principalValue φ b hb := by
  have haI : Ideal.span {a} ≠ (⊥ : Ideal (𝓞 F)) := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha
  have hbI : Ideal.span {b} ≠ (⊥ : Ideal (𝓞 F)) := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hb
  have h := EvenRayCharacter.integralUnit_mul (Ideal.span {a}) (Ideal.span {b}) haI hbI
  simp only [Ideal.span_singleton_mul_span_singleton] at h
  exact (congrArg φ h).trans (map_mul φ _ _)

lemma exists_nonzero_lift (N : ℕ) (hN : 0 < N)
    (x : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ Ideal.Quotient.mk (rationalModulusIdeal (𝓞 F) N) a = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  by_cases ha : a = 0
  · subst a
    refine ⟨(N : 𝓞 F), Nat.cast_ne_zero.mpr hN.ne', ?_⟩
    rw [map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  · exact ⟨a, ha, rfl⟩

def residueLift (N : ℕ) (hN : 0 < N)
    (u : ((𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)ˣ) : 𝓞 F :=
  Classical.choose (exists_nonzero_lift N hN (u : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N))

lemma residueLift_ne_zero (N : ℕ) (hN : 0 < N)
    (u : ((𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)ˣ) : residueLift N hN u ≠ 0 :=
  (Classical.choose_spec (exists_nonzero_lift N hN (u : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N))).1

lemma residueLift_spec (N : ℕ) (hN : 0 < N)
    (u : ((𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)ˣ) :
    Ideal.Quotient.mk (rationalModulusIdeal (𝓞 F) N) (residueLift N hN u) = (u : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N) :=
  (Classical.choose_spec (exists_nonzero_lift N hN (u : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N))).2

def KernelLaw (N : ℕ) : Prop := ∀ (a : 𝓞 F) (ha : a ≠ 0),
  a - 1 ∈ rationalModulusIdeal (𝓞 F) N → principalValue φ a ha = 1

lemma principalValue_eq (N : ℕ) (hN : 0 < N) (hk : KernelLaw φ N)
    (u : ((𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)ˣ)
    (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hqA : Ideal.Quotient.mk (rationalModulusIdeal (𝓞 F) N) a = (u : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N))
    (hqB : Ideal.Quotient.mk (rationalModulusIdeal (𝓞 F) N) b = (u : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)) :
    principalValue φ a ha = principalValue φ b hb := by
  let c := residueLift N hN u⁻¹
  have hc : c ≠ 0 := residueLift_ne_zero N hN u⁻¹
  have hqc : Ideal.Quotient.mk (rationalModulusIdeal (𝓞 F) N) c = (u⁻¹ : ((𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)ˣ) :=
    residueLift_spec N hN u⁻¹
  have hac : a*c - 1 ∈ rationalModulusIdeal (𝓞 F) N := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, hqA, hqc, map_one, Units.mul_inv, sub_self]
  have hbc : b*c - 1 ∈ rationalModulusIdeal (𝓞 F) N := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, hqB, hqc, map_one, Units.mul_inv, sub_self]
  have hA := hk (a*c) (mul_ne_zero ha hc) hac
  have hB := hk (b*c) (mul_ne_zero hb hc) hbc
  rw [principalValue_mul φ a c ha hc] at hA
  rw [principalValue_mul φ b c hb hc] at hB
  exact mul_right_cancel (hA.trans hB.symm)

def residueHom (N : ℕ) (hN : 0 < N) (hk : KernelLaw φ N) :
    ((𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)ˣ →* ℂˣ where
  toFun u := principalValue φ (residueLift N hN u) (residueLift_ne_zero N hN u)
  map_one' := by
    apply hk
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_one, residueLift_spec, Units.val_one, sub_self]
  map_mul' u v := by
    rw [← principalValue_mul]
    apply principalValue_eq φ N hN hk (u*v)
    · exact residueLift_spec N hN (u*v)
    · rw [map_mul, residueLift_spec, residueLift_spec, Units.val_mul]

lemma residueHom_spec (N : ℕ) (hN : 0 < N) (hk : KernelLaw φ N)
    (a : 𝓞 F) (ha : a ≠ 0)
    (u : ((𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)ˣ)
    (hq : Ideal.Quotient.mk (rationalModulusIdeal (𝓞 F) N) a = (u : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)) :
    residueHom φ N hN hk u = principalValue φ a ha :=
  principalValue_eq φ N hN hk u _ a (residueLift_ne_zero N hN u) ha
    (residueLift_spec N hN u) hq

end PrimeDegreePackets.PrincipalRay
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_ZetaOrder
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

def canonicalRealEmbeddings (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] : OrderedEmbeddings (degreePred K + 1) K := by
  letI : Algebra.IsAlgebraic ℚ K := NumberField.isAlgebraic K
  letI : Algebra.IsSeparable ℚ K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let σ : EmbeddingOrder K (degreePred K + 1) :=
    (Fintype.equivFinOfCardEq (by rw [AlgHom.card, degreePred_spec K])).symm
  exact σ.toRealOrder

/-- The zero order of the continued Dedekind zeta function, using a
fixed embedding ordering and no removed primes. -/
def zetaZeroOrder (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (β : ℝ) : WithTop ℤ :=
  meromorphicOrderAt
    (cosetMeromorphic (canonicalRealEmbeddings K) (degreePred_spec K) 1) (β : ℂ)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_SubfieldOrders
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteNormalClosure_numberField
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

/-- An integer-valued version of the continued zeta order. -/
def zetaMultiplicity (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (β : ℝ) : ℤ :=
  (zetaZeroOrder K β).untopD 0

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [NumberField.IsTotallyReal E]

attribute [local instance] OAI.DukePrimeDegree.instIsTotallyRealSubtypeMemIntermediateFieldFixedField_solutions
def fixedFieldMultiplicity (β : ℝ) (H : Subgroup (E ≃ₐ[F] E)) : ℤ :=
  zetaMultiplicity (IntermediateField.fixedField H) β

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_PrimeBlockRationality
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

def rationalRowSpace {n : ℕ} (g : G n) : Submodule ℚ (Fin n → ℝ) :=
  LinearMap.range (rationalRowMap g.val)

instance instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace {n : ℕ} (g : G n) : FiniteDimensional ℚ (rationalRowSpace g) :=
  Module.Finite.range _

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_LatticeCentralizer
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Centralizers of actual lattice stabilizers

The matrix centralizer of an arbitrary family of rational matrices is
spanned over `ℝ` by its rational matrices. Finite dimensionality reduces
the family to a basis of its rational span. This applies, in particular,
to the integral stabilizer of a homogeneous orbit in the lattice space.
The identification of that centralizer with the real block algebra is
kept separate from this rational linear algebra statement.
-/

noncomputable section
open Matrix Module Set
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- Integral elements whose conjugates lie in the given actual orbit
group. These are precisely its lattice stabilizer in matrix coordinates. -/
def latticeOrbitStabilizer {n : ℕ} (g : G n) (H : Subgroup (G n)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin n) ℤ) :=
  H.comap ((MulAut.conj g⁻¹).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)))

/-- The rational matrices of the actual integral orbit stabilizer. -/
def latticeStabilizerMatrix {n : ℕ} (g : G n) (H : Subgroup (G n))
    (γ : latticeOrbitStabilizer g H) : Matrix (Fin n) (Fin n) ℚ :=
  γ.val.val.map (Int.castRingHom ℚ)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ConjugationOrbit
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conjugation maps on actual lattice orbit quotients

A matrix commuting with the lattice stabilizer defines a continuous
conjugation map on the corresponding homogeneous orbit quotient. Right
invariance of a measure on that quotient gives conjugation invariance of
its pushforward. This is the geometric bridge used by the elementary
matrix-density argument.
-/

noncomputable section
open MeasureTheory Filter Set Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma slMatrixConjugation_eq_self {n : ℕ} (h : G n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hc : Commute M h.val) : slMatrixConjugation h M = M := by
  change h⁻¹.val * M * h.val = M
  rw [mul_assoc, hc.eq, ← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_OrbitRationality
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational block centralizers from finite-volume lattice orbits

The rational matrices in the integral orbit-stabilizer centralizer span
its real centralizer. Conjugation by the actual lattice matrix transports
this statement to the embedding coordinates. Finite-orbit density then
identifies this transported centralizer with the block-scalar algebra.
-/

noncomputable section
open Matrix Module Set MeasureTheory
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def slMatrixConjugationHom {n : ℕ} (g : G n) :
    Matrix (Fin n) (Fin n) ℝ →* Matrix (Fin n) (Fin n) ℝ where
  toFun := slMatrixConjugation g
  map_one' := by
    simp only [slMatrixConjugation, mul_one, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  map_mul' A B := by
    have hg : g.val * g⁻¹.val = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    simp only [slMatrixConjugation, mul_assoc,
      ← mul_assoc g.val g⁻¹.val, hg, one_mul]

def slMatrixConjugationLinear {n : ℕ} (g : G n) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.mulLeftRight ℝ (g⁻¹.val, g.val)

lemma slMatrixConjugation_inverse {n : ℕ} (g : G n)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    slMatrixConjugation g (slMatrixConjugation g⁻¹ M) = M := by
  rw [← slMatrixConjugation_mul, inv_mul_cancel, slMatrixConjugation_one]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockRootGroup
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The group generated by the roots within each block

The finite-orbit fixed-vector obstruction excludes singleton blocks.
Without singleton blocks, the full matrix commutant of the root-generated
group is exactly the block-scalar algebra. Its full normalizer therefore
lies in the scalar-algebra normalizer used in orbit reduction.
-/

noncomputable section
open Matrix Set MeasureTheory
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def blockRootGroup {n : ℕ} (r : Setoid (Fin n)) : Subgroup (G n) :=
  Subgroup.closure {g | ∃ (i j : Fin n) (hij : i ≠ j) (t : ℝ),
    r i j ∧ g = Matrix.SpecialLinearGroup.transvection hij t}

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZeroSeparation
attribute [-instance] _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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


namespace PrimeDegreePackets
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]



lemma anchorNormalize_finite (ν : Measure β) [IsFiniteMeasure ν]
    (J : Set β) (hJ : ν J ≠ 0) : IsFiniteMeasure (anchorNormalize ν J) := by
  constructor
  change (ν J)⁻¹ * ν univ < ∞
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hJ))
    (measure_lt_top ν univ)

 

theorem anchorNormalize_restrict (p q : Measure β) [IsFiniteMeasure p] [IsFiniteMeasure q]
    {V J : Set β} (hJ : MeasurableSet J) (hJV : J ⊆ V)
    (hrel : q V • p = q.restrict V) (hqJ : q J ≠ 0) :
    p J ≠ 0 ∧ anchorNormalize p J = (anchorNormalize q J).restrict V := by
  have hm : q V * p J = q J := by
    have H := congrArg (fun ν : Measure β => ν J) hrel
    simpa only [Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hJ,
      inter_eq_left.mpr hJV] using H
  have hpJ : p J ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hm
    exact hqJ hm.symm
  have he : (q J)⁻¹ * q V = (p J)⁻¹ := by
    rw [←hm,ENNReal.mul_inv (Or.inr (measure_ne_top p J))
      (Or.inl (measure_ne_top q V))]
    rw [mul_right_comm,ENNReal.inv_mul_cancel
      (ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hqJ) (measure_mono hJV)))
      (measure_ne_top q V),one_mul]
  refine ⟨hpJ,?_⟩
  unfold anchorNormalize
  rw [Measure.restrict_smul,←hrel,smul_smul,he]



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafNormalization
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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


lemma rootLeafWindow_mono (R : ℝ) : Monotone (rootLeafWindow R) := by
  intro a b hab
  have h : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
  exact Ioo_subset_Ioo (by linarith) (by linarith)

lemma rootLeafWindow_cover (R : ℝ) : ⋃ m, rootLeafWindow R m = univ := by
  apply Set.eq_univ_of_forall
  intro t
  obtain ⟨m,hm⟩ := exists_nat_gt (|t|+|R|)
  apply mem_iUnion.mpr
  refine ⟨m,?_,?_⟩
  · have h₁ := neg_abs_le t
    have h₂ := neg_abs_le R
    linarith
  · have h₁ := le_abs_self t
    have h₂ := neg_abs_le R
    linarith

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootLeaves
attribute [-instance] _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

lemma anchorNormalize_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) (e : α ≃ᵐ β) (J : Set α) :
    anchorNormalize (ν.map e) (e '' J) = (anchorNormalize ν J).map e := by
  unfold anchorNormalize
  rw [e.measurableEmbedding.map_apply,e.injective.preimage_image,
    Measure.map_smul]

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafSupport
attribute [-instance] _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

 

lemma isSFiniteKernel_of_pointwise_finite {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (κ : Kernel α β) (hκ : ∀ a, κ a univ < ∞) : IsSFiniteKernel κ := by
  let U : ℕ → Set α := fun m => {a | κ a univ < m}
  let V := disjointed U
  have hU (m : ℕ) : MeasurableSet (U m) :=
    measurableSet_lt (κ.measurable_coe MeasurableSet.univ) measurable_const
  have hV (m : ℕ) : MeasurableSet (V m) := MeasurableSet.disjointed hU m
  let κs : ℕ → Kernel α β := fun m => Kernel.piecewise (hV m) κ 0
  refine ⟨κs,?_,?_⟩
  · intro m
    refine ⟨(m : ℝ≥0∞),ENNReal.natCast_lt_top m,?_⟩
    intro a
    change (if a ∈ V m then κ a else 0) univ ≤ (m : ℝ≥0∞)
    split_ifs with ha
    · exact (disjointed_subset U m ha).le
    · change 0 ≤ (m : ℝ≥0∞)
      exact bot_le
  · ext a T hT
    obtain ⟨m,hm⟩ := ENNReal.exists_nat_gt (hκ a).ne
    have ha : a ∈ ⋃ k, V k := by
      rw [iUnion_disjointed]
      exact mem_iUnion.mpr ⟨m,hm⟩
    obtain ⟨k,hk⟩ := mem_iUnion.mp ha
    rw [Kernel.sum_apply' _ _ hT,tsum_eq_single k]
    · change κ a T = (if a ∈ V k then κ a else 0) T
      rw [ite_eq_left hk]
    · intro l hl
      have hl' : a ∉ V l := fun hal => (disjoint_disjointed U hl).le_bot ⟨hal,hk⟩
      change (if a ∈ V l then κ a else 0) T = 0
      rw [ite_eq_right hl']
      rfl

 

lemma isSFiniteKernel_of_finite_exhaustion {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (κ : Kernel α β) (W : ℕ → Set β)
    (hW : ∀ m, MeasurableSet (W m)) (hcov : ⋃ m, W m = univ)
    (hfin : ∀ a m, κ a (W m) < ∞) : IsSFiniteKernel κ := by
  let V := disjointed W
  have hV (m : ℕ) : MeasurableSet (V m) := MeasurableSet.disjointed hW m
  let κs : ℕ → Kernel α β := fun m => κ.restrict (hV m)
  have (m : ℕ) : IsSFiniteKernel (κs m) := by
    apply isSFiniteKernel_of_pointwise_finite
    intro a
    change (κ a).restrict (V m) univ < ∞
    rw [Measure.restrict_apply MeasurableSet.univ,univ_inter]
    exact (measure_mono (disjointed_subset W m)).trans_lt (hfin a m)
  have he : κ = Kernel.sum κs := by
    ext a T hT
    exact congrArg (fun ν : Measure β => ν T) (measure_eq_sum_disjointed (κ a) W hW hcov)
  rw [he]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)


lemma locallyFiniteRealVersion_eq {α : Type*} [MeasurableSpace α] (κ : Kernel α ℝ)
    (a : α) [IsLocallyFiniteMeasure (κ a)] : locallyFiniteRealVersion κ a = κ a := by
  apply ite_eq_left
  intro m
  exact isCompact_Icc.measure_lt_top

end PrimeDegreePackets


namespace PrimeDegreePackets


lemma centerRealMeasure_ball (ν : Measure ℝ) (t r : ℝ) :
    centerRealMeasure ν t (Metric.ball 0 r) = ν (Metric.ball t r) := by
  rw [centerRealMeasure,Measure.map_apply (Homeomorph.subRight t).measurable Metric.isOpen_ball.measurableSet]
  congr 1
  ext u
  simp only [Set.mem_preimage,Metric.mem_ball,Homeomorph.coe_subRight,Real.dist_eq]
  rw [sub_zero]

instance centerRealMeasure_locallyFinite (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (t : ℝ) :
    IsLocallyFiniteMeasure (centerRealMeasure ν t) := by
  apply locallyFinite_of_finite_real_windows
  intro m
  rw [centerRealMeasure,Measure.map_apply (Homeomorph.subRight t).measurable measurableSet_Icc]
  exact ((Homeomorph.subRight t).isCompact_preimage.mpr isCompact_Icc).measure_lt_top



lemma basedRealMeasure_ball_one (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (t : ℝ)
    (ht : 0 < ν (Metric.ball t 1)) : basedRealMeasure ν t (Metric.ball 0 1) = 1 := by
  change (centerRealMeasure ν t (Metric.ball 0 1))⁻¹ * centerRealMeasure ν t (Metric.ball 0 1) = 1
  rw [centerRealMeasure_ball]
  exact ENNReal.inv_mul_cancel ht.ne' measure_ball_lt_top.ne

lemma basedRealMeasure_locallyFinite (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (t : ℝ)
    (ht : 0 < ν (Metric.ball t 1)) : IsLocallyFiniteMeasure (basedRealMeasure ν t) := by
  apply locallyFinite_of_finite_real_windows
  intro m
  change (centerRealMeasure ν t (Metric.ball 0 1))⁻¹ *
    centerRealMeasure ν t (Icc (-(m : ℝ)) m) < ∞
  rw [centerRealMeasure_ball]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr ht) isCompact_Icc.measure_lt_top

 

def centerRealKernel {α : Type*} [MeasurableSpace α] (κ : Kernel α ℝ)
    [IsSFiniteKernel κ] : Kernel (α × ℝ) ℝ where
  toFun z := centerRealMeasure (κ z.1) z.2
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    have H := Kernel.measurable_kernel_prodMk_left (κ := Kernel.prodMkRight ℝ κ)
      ((measurable_snd.sub measurable_fst.snd) hS)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    exact Measure.map_apply (Homeomorph.subRight z.2).measurable hS

 

def basedRealKernel {α : Type*} [MeasurableSpace α] (κ : Kernel α ℝ)
    [IsSFiniteKernel κ] : Kernel (α × ℝ) ℝ where
  toFun z := basedRealMeasure (κ z.1) z.2
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    change Measurable (fun z => (centerRealKernel κ z (Metric.ball 0 1))⁻¹ * centerRealKernel κ z S)
    exact (centerRealKernel κ |>.measurable_coe Metric.isOpen_ball.measurableSet).inv.mul
      (centerRealKernel κ |>.measurable_coe hS)

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma anchorNormalize_smul {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (J : Set α) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcT : c ≠ ∞) :
    anchorNormalize (c • ν) J = anchorNormalize ν J := by
  unfold anchorNormalize
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.mul_inv (Or.inl hc0) (Or.inl hcT),smul_smul]
  congr 1
  rw [mul_right_comm,ENNReal.inv_mul_cancel hc0 hcT,one_mul]

lemma anchorNormalize_restrict_comm {α : Type*} [MeasurableSpace α]
    (ν : Measure α) {J W : Set α} (hJ : MeasurableSet J) (hJW : J ⊆ W) :
    anchorNormalize (ν.restrict W) J = (anchorNormalize ν J).restrict W := by
  unfold anchorNormalize
  rw [Measure.restrict_apply hJ,inter_eq_left.mpr hJW,Measure.restrict_smul]

lemma anchorNormalize_twice {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (J W : Set α) (hW0 : ν W ≠ 0) (hWT : ν W ≠ ∞) :
    anchorNormalize (anchorNormalize ν W) J = anchorNormalize ν J :=
  anchorNormalize_smul ν J _ (ENNReal.inv_ne_zero.mpr hWT) (ENNReal.inv_ne_top.mpr hW0)

lemma centerRealMeasure_smul (ν : Measure ℝ) (c : ℝ≥0∞) (t : ℝ) :
    centerRealMeasure (c • ν) t = c • centerRealMeasure ν t :=
  Measure.map_smul c _ _

lemma basedRealMeasure_smul (ν : Measure ℝ) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcT : c ≠ ∞) (t : ℝ) :
    basedRealMeasure (c • ν) t = basedRealMeasure ν t := by
  unfold basedRealMeasure
  rw [centerRealMeasure_smul,anchorNormalize_smul _ _ _ hc0 hcT]

lemma centerRealMeasure_scaling (ν : Measure ℝ) (c t : ℝ) (hc : c ≠ 0) :
    centerRealMeasure (ν.map (Homeomorph.mulLeft₀ c hc)) (c*t) =
      (centerRealMeasure ν t).map (Homeomorph.mulLeft₀ c hc) := by
  unfold centerRealMeasure
  rw [Measure.map_map (Homeomorph.subRight (c*t)).measurable (Homeomorph.mulLeft₀ c hc).measurable,
    Measure.map_map (Homeomorph.mulLeft₀ c hc).measurable (Homeomorph.subRight t).measurable]
  congr 1
  funext x
  change c*x-c*t=c*(x-t)
  ring

 

lemma basedRealMeasure_scaling (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (c t : ℝ) (hc : c ≠ 0) (ht : 0 < ν (Metric.ball t 1)) :
    basedRealMeasure (ν.map (Homeomorph.mulLeft₀ c hc)) (c*t) =
      anchorNormalize ((basedRealMeasure ν t).map (Homeomorph.mulLeft₀ c hc)) (Metric.ball 0 1) := by
  unfold basedRealMeasure
  rw [centerRealMeasure_scaling]
  unfold anchorNormalize
  rw [Measure.map_smul]
  exact (anchorNormalize_smul _ _ _
    (ENNReal.inv_ne_zero.mpr (by rw [centerRealMeasure_ball]; exact measure_ball_lt_top.ne))
    (ENNReal.inv_ne_top.mpr (by rw [centerRealMeasure_ball]; exact ht.ne'))).symm

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafAnchors
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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
variable {n : ℕ} {i j k l : Fin n} (hij : i ≠ j)

abbrev RootSliceOverlap (i j k l : Fin n) (γ : G n) :=
  {s : RootSlice i j k // (γ * s.val).1 l i ≠ 0}

def rootTransitionPivot (γ : G n) (s : RootSliceOverlap i j k l γ) : RootPivot i l :=
  ⟨γ * s.val.val,s.prop⟩

def rootTransitionTime (γ : G n) (s : RootSliceOverlap i j k l γ) : ℝ :=
  rootParameter i j l (γ * s.val.val)

lemma continuous_rootTransitionPivot (γ : G n) :
    Continuous (rootTransitionPivot (i := i) (j := j) (k := k) (l := l) γ) := by
  apply Continuous.subtype_mk
  exact continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)

lemma continuous_rootTransitionTime (γ : G n) :
    Continuous (rootTransitionTime (i := i) (j := j) (k := k) (l := l) γ) :=
  continuous_rootParameter.comp (continuous_rootTransitionPivot γ)

end PrimeDegreePackets


namespace PrimeDegreePackets


lemma centerRealMeasure_translate (ν : Measure ℝ) (t u : ℝ) :
    centerRealMeasure (ν.map (Homeomorph.addRight u)) (t+u) = centerRealMeasure ν t := by
  unfold centerRealMeasure
  rw [Measure.map_map (Homeomorph.subRight (t+u)).measurable (Homeomorph.addRight u).measurable]
  congr 1
  funext x
  change (x+u)-(t+u)=x-t
  ring

lemma basedRealMeasure_translate (ν : Measure ℝ) (t u : ℝ) :
    basedRealMeasure (ν.map (Homeomorph.addRight u)) (t+u) = basedRealMeasure ν t := by
  unfold basedRealMeasure
  rw [centerRealMeasure_translate]


end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ConditionalFibers
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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
variable {n : ℕ} {i j k l : Fin n} {hij : i ≠ j}

lemma rootSliceOverlap_isOpen (γ : G n) :
    IsOpen {s : RootSlice i j k | (γ * s.val).1 l i ≠ 0} := by
  apply isOpen_ne_fun _ continuous_const
  have hc : Continuous (fun s : RootSlice i j k =>
      ((γ * s.val) : Matrix (Fin n) (Fin n) ℝ)) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous.comp
      (show Continuous (fun s : RootSlice i j k => γ * s.val) from
        continuous_const.mul continuous_subtype_val)
  exact (continuous_apply i).comp ((continuous_apply l).comp hc)

end PrimeDegreePackets


namespace PrimeDegreePackets
variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace δ]

lemma conditional_restrict_normalized [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (T : Set (α × β)) (hT : MeasurableSet T) :
    ∀ᵐ a ∂(ρ.restrict T).fst,
      ρ.condKernel a (Prod.mk a ⁻¹' T) ≠ 0 ∧
      (ρ.restrict T).condKernel a =
        (anchorNormalize (ρ.condKernel a) (Prod.mk a ⁻¹' T)).restrict (Prod.mk a ⁻¹' T) := by
  let w := fun a => ρ.condKernel a (Prod.mk a ⁻¹' T)
  have hw : Measurable w := Kernel.measurable_kernel_prodMk_left hT
  have hp : ∀ᵐ a ∂(ρ.restrict T).fst, w a ≠ 0 := by
    rw [conditional_restrict_marginal ρ T hT]
    exact (ae_withDensity_iff hw).mpr (ae_of_all _ fun _ h => h)
  have H : ∀ᵐ a ∂(ρ.restrict T).fst,
      w a • (ρ.restrict T).condKernel a = (ρ.condKernel a).restrict (Prod.mk a ⁻¹' T) := by
    rw [conditional_restrict_marginal ρ T hT]
    exact (withDensity_absolutelyContinuous ρ.fst w).ae_le (conditional_restrict_fibers ρ T hT)
  filter_upwards [hp,H] with a hpa ha
  refine ⟨hpa,?_⟩
  have he := congrArg (fun ν : Measure β => (w a)⁻¹ • ν) ha
  rw [smul_smul,ENNReal.inv_mul_cancel hpa (measure_ne_top _ _),one_smul] at he
  simpa only [anchorNormalize,Measure.restrict_smul] using he

 

theorem conditional_overlap_normalized [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace δ] [Nonempty δ]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (σ : Measure (γ × δ)) [IsFiniteMeasure σ]
    (T : Set (α × β)) (hT : MeasurableSet T)
    (W : Set (γ × δ)) (hW : MeasurableSet W)
    (e : α ≃ᵐ γ) (F : α × β → δ) (hF : Measurable F)
    (he : (ρ.restrict T).map (fun z => (e z.1,F z)) = σ.restrict W) :
    ∀ᵐ a ∂(ρ.restrict T).fst,
      ρ.condKernel a (Prod.mk a ⁻¹' T) ≠ 0 ∧
      σ.condKernel (e a) (Prod.mk (e a) ⁻¹' W) ≠ 0 ∧
      ((anchorNormalize (ρ.condKernel a) (Prod.mk a ⁻¹' T)).restrict (Prod.mk a ⁻¹' T)).map
        (fun b => F (a,b)) =
      (anchorNormalize (σ.condKernel (e a)) (Prod.mk (e a) ⁻¹' W)).restrict (Prod.mk (e a) ⁻¹' W) := by
  have Hρ := conditional_restrict_normalized ρ T hT
  have Hσ := conditional_restrict_normalized σ W hW
  have hm := congrArg Measure.fst he
  rw [fst_map_fibers _ e F hF] at hm
  rw [←hm] at Hσ
  have Hσ' := ae_of_ae_map e.measurable.aemeasurable Hσ
  have Hcov := conditional_map_fibers (ρ.restrict T) e F hF
  filter_upwards [Hρ,Hσ',Hcov] with a ha hb hc
  simp only [he] at hc
  refine ⟨ha.1,hb.1,?_⟩
  rw [←ha.2,←hb.2]
  exact hc.symm

end PrimeDegreePackets


namespace PrimeDegreePackets
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma anchorNormalize_map (ν : Measure α) (e : α ≃ᵐ β) {J : Set α}
    (hJ : MeasurableSet J) :
    (anchorNormalize ν J).map e = anchorNormalize (ν.map e) (e '' J) := by
  unfold anchorNormalize
  rw [Measure.map_smul,Measure.map_apply e.measurable
    (e.measurableEmbedding.measurableSet_image.mpr hJ),e.preimage_image]

lemma anchorNormalize_congr_restriction (ν p : Measure α) {D J : Set α}
    (hJ : MeasurableSet J) (hJD : J ⊆ D)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcT : c ≠ ∞)
    (he : ν.restrict D = c • p) :
    (anchorNormalize ν J).restrict D = anchorNormalize p J := by
  rw [←anchorNormalize_restrict_comm ν hJ hJD,he,anchorNormalize_smul _ _ _ hc0 hcT]

lemma anchorNormalize_reanchor_map (p : Measure α) (q : Measure β)
    (e : α ≃ᵐ β) {V : Set α} {W : Set β} {J : Set α}
    (hJ : MeasurableSet J) (hJV : J ⊆ V) (hJW : e '' J ⊆ W)
    (hpV0 : p V ≠ 0) (hpVT : p V ≠ ∞) (hqW0 : q W ≠ 0) (hqWT : q W ≠ ∞)
    (he : ((anchorNormalize p V).restrict V).map e = (anchorNormalize q W).restrict W) :
    ((anchorNormalize p J).restrict V).map e = (anchorNormalize q (e '' J)).restrict W := by
  have H := congrArg (fun ρ : Measure β => anchorNormalize ρ (e '' J)) he
  rw [←anchorNormalize_map _ e hJ,anchorNormalize_restrict_comm _ hJ hJV,
    anchorNormalize_twice _ _ _ hpV0 hpVT,
    anchorNormalize_restrict_comm _ (e.measurableEmbedding.measurableSet_image.mpr hJ) hJW,
    anchorNormalize_twice _ _ _ hqW0 hqWT] at H
  exact H

 

theorem projective_extensions_overlap
    (ν p : Measure α) (η q : Measure β) (e : α ≃ᵐ β)
    {D V J : Set α} {E W : Set β}
    (hD : MeasurableSet D) (hE : MeasurableSet E)
    (hJ : MeasurableSet J) (hJD : J ⊆ D) (hJV : J ⊆ V)
    (hJE : e '' J ⊆ E) (hJW : e '' J ⊆ W)
    (c d : ℝ≥0∞) (hc0 : c ≠ 0) (hcT : c ≠ ∞) (hd0 : d ≠ 0) (hdT : d ≠ ∞)
    (hν : ν.restrict D = c • p) (hη : η.restrict E = d • q)
    (hpV0 : p V ≠ 0) (hpVT : p V ≠ ∞) (hqW0 : q W ≠ 0) (hqWT : q W ≠ ∞)
    (he : ((anchorNormalize p V).restrict V).map e = (anchorNormalize q W).restrict W) :
    ((anchorNormalize ν J).restrict (V ∩ D)).map e =
      (anchorNormalize η (e '' J)).restrict (W ∩ E) := by
  have Hν := anchorNormalize_congr_restriction ν p hJ hJD c hc0 hcT hν
  have Hη := anchorNormalize_congr_restriction η q
    (e.measurableEmbedding.measurableSet_image.mpr hJ) hJE d hd0 hdT hη
  have H := anchorNormalize_reanchor_map p q e hJ hJV hJW hpV0 hpVT hqW0 hqWT he
  rw [←Hν,←Hη] at H
  simpa only [Measure.restrict_restrict' hD,Measure.restrict_restrict' hE] using H

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafTransitions
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

lemma translated_window_chain_cover (R S u : ℝ) :
    ⋃ m : ℕ, ((Homeomorph.addRight u) '' rootLeafWindow R m ∩ rootLeafWindow S m) = univ := by
  apply Set.eq_univ_of_forall
  intro t
  have h₁ : t-u ∈ ⋃ m, rootLeafWindow R m := by rw [rootLeafWindow_cover]; trivial
  have h₂ : t ∈ ⋃ m, rootLeafWindow S m := by rw [rootLeafWindow_cover]; trivial
  obtain ⟨a,ha⟩ := mem_iUnion.mp h₁
  obtain ⟨b,hb⟩ := mem_iUnion.mp h₂
  refine mem_iUnion.mpr ⟨max a b,⟨t-u,rootLeafWindow_mono R (le_max_left _ _) ha,?_⟩,
    rootLeafWindow_mono S (le_max_right _ _) hb⟩
  change (t-u)+u=t
  ring

end PrimeDegreePackets

open scoped Matrix Topology Classical ENNReal
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_AmbientLeaves
attribute [-instance] _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

lemma basedRealMeasure_ball_pos (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (t r : ℝ) (hr : 0 < ν (Metric.ball t r)) :
    0 < basedRealMeasure ν t (Metric.ball 0 r) := by
  change 0 < (centerRealMeasure ν t (Metric.ball 0 1))⁻¹ * centerRealMeasure ν t (Metric.ball 0 r)
  rw [centerRealMeasure_ball,centerRealMeasure_ball]
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne) hr.ne'



end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ScalingCovariance
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

lemma normalized_realScaling_ball (ν : Measure ℝ) (c r : ℝ) (hc : 0 < c) :
    anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)
      (Metric.ball 0 r) = (ν (Metric.ball 0 (1/c)))⁻¹ * ν (Metric.ball 0 (r/c)) := by
  change (ν.map (Homeomorph.mulLeft₀ c hc.ne') (Metric.ball 0 1))⁻¹ *
    ν.map (Homeomorph.mulLeft₀ c hc.ne') (Metric.ball 0 r) = _
  rw [Measure.map_apply (Homeomorph.mulLeft₀ c hc.ne').measurable
      Metric.isOpen_ball.measurableSet,
    Measure.map_apply (Homeomorph.mulLeft₀ c hc.ne').measurable
      Metric.isOpen_ball.measurableSet,
    realScaling_preimage_ball c 1 hc,realScaling_preimage_ball c r hc]


end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CentralizerFlow
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small centralizer factors in late diagonal returns

The root-pair centralizer supplies a scalar double block and a complementary
matrix. A fixed neighborhood controls that complementary matrix; late
neutral diagonal times separate its spectrum and keep the scalar away
from the rational units.
-/

noncomputable section
open Set Filter Matrix
open scoped Classical Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def complementaryMatrix {n m : ℕ} (e : Fin n ≃ Fin 2 ⊕ Fin m)
    (g : G n) : Matrix (Fin m) (Fin m) ℝ :=
  fun r s => g.val (e.symm (Sum.inr r)) (e.symm (Sum.inr s))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafMeasurableBad
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Measurable bad sets for intrinsic leaf averages

Strict bad inequalities at rational radii define a measurable set.
Its complement controls every real radius, by continuity from above.
The diagonal scaling estimate bounds this set uniformly over all radii.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

def rootHitTimes {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (E : Set (X n)) (x : X n) : Set ℝ :=
  {u | rightAction x (Matrix.SpecialLinearGroup.transvection hij u) ∈ E}

def rootRationalBad {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (κ : Kernel (X n) ℝ) (E : Set (X n)) (c : ℝ≥0∞) (R : ℝ) : Set (X n) :=
  {x | ∃ q : ℚ, (0 < (q : ℝ) ∧ (q : ℝ) ≤ R) ∧
    c * κ x (closedBall 0 (q : ℝ)) < κ x (rootHitTimes hij E x ∩ closedBall 0 (q : ℝ))}

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingDiagonal
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

def rootPairFlow {n : ℕ} (i j : Fin n) (t : ℝ) : G n :=
  diagonalOneParameter (rootPairWeights i j) (rootPairWeights_sum i j) t

def rootPairConjugate {n : ℕ} (i j : Fin n) (t : ℝ) (g : G n) : G n :=
  rootPairFlow i j t * g * rootPairFlow i j (-t)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_LeafFlowCovariance
attribute [-instance] _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

def normalizedRescaledRealKernel {Y : Type*} [MeasurableSpace Y]
    (κ : Kernel Y ℝ) [IsSFiniteKernel κ] (c : Y → ℝ) (hc : Measurable c) :
    Kernel Y ℝ where
  toFun y := anchorNormalize (rescaledRealKernel κ c hc y) (Metric.ball 0 1)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    exact ((rescaledRealKernel κ c hc).measurable_coe
      Metric.isOpen_ball.measurableSet).inv.mul
        ((rescaledRealKernel κ c hc).measurable_coe hS)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_MatrixVelocitySpace
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual vector space of subgroup velocities

Velocities are derivatives of genuine curves in the subgroup at its
identity. Multiplication adds velocities and a linear reparametrization
scales them. Conjugating the subgroup conjugates this vector space.
No Lie-subgroup or homogeneous-support assertion is assumed here.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The finite-dimensional real subspace comes from actual subgroup
curves. In particular, it is not an arbitrary assigned frame. -/
def matrixVelocitySpace {n : ℕ} (H : Subgroup (G n)) :
    Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {V | ∃ γ : ℝ → G n, (∀ t, γ t ∈ H) ∧ HasIdentityMatrixDerivative γ V}
  zero_mem' := by
    refine ⟨fun _ => 1, fun _ => H.one_mem, rfl, ?_⟩
    intro i j
    simpa only [Matrix.zero_apply] using hasDerivAt_const (0 : ℝ)
      ((1 : G n).val i j)
  add_mem' := by
    rintro V W ⟨γ, hγH, hγ⟩ ⟨δ, hδH, hδ⟩
    exact ⟨fun t => γ t * δ t, fun t => H.mul_mem (hγH t) (hδH t), hγ.mul hδ⟩
  smul_mem' := by
    rintro c V ⟨γ, hγH, hγ⟩
    exact ⟨fun t => γ (c * t), fun t => hγH _, hγ.reparametrize c⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_MautnerRootPair
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mautner's root-pair calculation inside the actual acting subgroup

The subgroup parameter is essential: the ambient finite measure is not
assumed invariant under all of SLₙ. The two opposite roots belong to its
invariant block group, and the isometric action is restricted to that
group. A concrete two-by-two identity supplies the diagonal fixed vector.
-/

noncomputable section
open Matrix Filter Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The elementary Gauss identity used in the Mautner argument. -/
lemma root_pair_gauss_identity {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (a s : ℝ) (ha : a ≠ 0) (hs : s ≠ 0) :
    Matrix.SpecialLinearGroup.transvection hij s *
      Matrix.SpecialLinearGroup.transvection hij.symm ((a - 1) / s) *
      Matrix.SpecialLinearGroup.transvection hij (-s / a) =
    Matrix.SpecialLinearGroup.transvection hij.symm ((a - 1) / (s * a)) *
      Matrix.SpecialLinearGroup.diag2n hij a ha := by
  apply Subtype.ext
  ext p q
  rw [root_mul_entry, root_left_mul_entry, root_left_mul_entry]
  change _ = (Matrix.transvection j i ((a - 1) / (s * a)) *
    Matrix.diagonal (fun k => if k = i then a else if k = j then a⁻¹ else 1)) p q
  rw [Matrix.mul_diagonal]
  simp only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection,
    Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have hp : p = i ∨ p = j ∨ (p ≠ i ∧ p ≠ j) := by tauto
  have hq : q = i ∨ q = j ∨ (q ≠ i ∧ q ≠ j) := by tauto
  rcases hp with rfl | rfl | ⟨hpi, hpj⟩ <;>
    rcases hq with rfl | rfl | ⟨hqi, hqj⟩
  all_goals simp_all [eq_comm]
  all_goals field_simp [ha, hs] <;> ring

lemma diag2n_mem_of_opposite_roots {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (H : Subgroup (G n))
    (hU : ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ H)
    (hV : ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij.symm t ∈ H)
    (a : ℝ) (ha : a ≠ 0) : Matrix.SpecialLinearGroup.diag2n hij a ha ∈ H := by
  have he := root_pair_gauss_identity hij a 1 ha one_ne_zero
  have hmem := H.mul_mem (H.mul_mem (hU 1) (hV ((a - 1) / 1))) (hU (-1 / a))
  rw [he] at hmem
  have hcancel := H.mul_mem (H.inv_mem (hV ((a - 1) / (1 * a)))) hmem
  simpa only [inv_mul_cancel_left] using hcancel

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingScale
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A first scale for noncentral root shearing

Every matrix outside a root centralizer has a finite positive first time
at which its conjugation displacement reaches a prescribed size. Before
that time all matrix entries remain uniformly controlled. This is the
stopping-time normalization used for the polynomial shearing argument.
-/

open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

def rootShearSize {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n) (t : ℝ) : ℝ :=
  ∑ r, ∑ s, |(Matrix.SpecialLinearGroup.transvection hij t * g *
    Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s - g.1 r s|

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingCompactness
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A nontrivial limit of normalized shearing

The normalized first shearing intervals provide bounded terminal
matrices. Finite-dimensional compactness supplies a convergent
subsequence, whose limit is nontrivial and centralizes the root group.
-/

open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

def slMatrixDifference {n : ℕ} (g h : G n) : ℝ :=
  ∑ r, ∑ s, |g.1 r s - h.1 r s|

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingHorosphere
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The horospherical shape of a normalized shearing limit

The limiting matrix differs from the identity only in the chosen row
and column, with unchanged diagonal. Its displacement is nilpotent of
order at most three. This is the precise horospherical direction used
in EKL (2006), Section 4.2, equations (4.6)--(4.8).
-/

noncomputable section
open Set Filter Matrix
open scoped BigOperators Classical Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def RootHorosphereShape {n : ℕ} (i j : Fin n) (h : G n) : Prop :=
  ∀ r s, (r ≠ i ∧ s ≠ j) ∨ r = s → h.val r s = (1 : Matrix (Fin n) (Fin n) ℝ) r s

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingKappa
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A scale for noncentral return matrices

The scale is the maximum of the diagonal difference and a homogeneous
off-diagonal size. The latter uses the square root of the quadratic
coefficient and a finite sum of the other linear coefficients. This
equivalent choice of norm gives exactly the two scaling regimes used in
EKL (2006), Lemma 4.6.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rootShearingOffDiagonalSize {n : ℕ} (i j : Fin n) (g : G n) : ℝ :=
  ∑ k, if k = i ∨ k = j then 0 else |g.val j k| + |g.val k i|

def rootShearingMovingSize {n : ℕ} (i j : Fin n) (g : G n) : ℝ :=
  Real.sqrt |g.val j i| + rootShearingOffDiagonalSize i j g

def rootShearingKappa {n : ℕ} (i j : Fin n) (g : G n) : ℝ :=
  max |g.val j j - g.val i i| (rootShearingMovingSize i j g)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingLogTime
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Divergence of the logarithmic shearing window

Noncentral return matrices approaching the identity have positive scale
tending to zero. Their logarithmic time window tends to infinity, and
the two exponential regimes have exactly the bounds needed for the
common-time selection theorem.
-/

noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def rootShearingLogTime {n : ℕ} (i j : Fin n) (g : G n) : ℝ :=
  -Real.log (rootShearingKappa i j g) / 4

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SmallCentralizer
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

def matrixClosedBall (n : ℕ) (r : ℝ) : Set (G n) :=
  (fun g : G n => g.val) ⁻¹' Metric.closedBall 1 r

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SmallReturns
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small quotient returns centralize both roots

For a fixed neutral return parameter, compact sets of possible small
return matrices give measurable sets of returning points. Conjugation in
the contracting direction preserves the single-root centralizer ball;
uniqueness of quotient lifts then identifies returning matrices exactly.
Poincaré recurrence proves the fixed-parameter form of EKL Lemma 4.2.
-/

noncomputable section
open Filter Set Matrix MeasureTheory
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def compactReturnSet {n : ℕ} (K : Set (G n)) (b : G n) : Set (X n) :=
  {x | ∃ g ∈ K, rightAction x g = rightAction x b}

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_StrongReturns
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous strong returns

The fixed-parameter small-return theorem extends to a whole subgroup by
separability and closedness. This removes the parameter-dependent null
sets in the exceptional-return argument of EKL (2006), Lemma 4.2.
-/

noncomputable section
open Filter Set Matrix MeasureTheory
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def singleRootCentralizer {n : ℕ} {i j : Fin n} (hij : i ≠ j) : Subgroup (G n) :=
  Subgroup.centralizer {Matrix.SpecialLinearGroup.transvection hij 1}

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralWeightSpace
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
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

def neutralSpaceDiagonal {n : ℕ} (i j : Fin n) :
    Multiplicative (neutralWeightSpace i j) →* G n where
  toFun u := diagonalOneParameter u.toAdd.val u.toAdd.property.1 1
  map_one' := by
    apply Subtype.ext
    simp [diagonalOneParameter]
  map_mul' u v :=
    diagonalOneParameter_add_weights _ _ u.toAdd.property.1 v.toAdd.property.1 1

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LatticeGroupDecomposition
attribute [-instance] _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The lattice group action and its ergodic components

Taking inverses writes the right lattice action as a left action.
Measurable ergodic decomposition gives probability components for each
closed matrix subgroup preserving the measure. Adjoining an invariant
subgroup to the diagonal action preserves invariance and ergodicity
of a diagonal-ergodic probability, as required by Margulis--Tomanov.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The left action corresponding to the actual right lattice action. -/
instance latticeSubgroupInverseAction {n : ℕ} (H : Subgroup (G n)) :
    MulAction H (X n) where
  smul h x := rightAction x (h.val)⁻¹
  one_smul x := by
    change rightAction x (1 : G n)⁻¹ = x
    simp
  mul_smul h k x := by
    change rightAction x (h.val * k.val)⁻¹ =
      rightAction (rightAction x k.val⁻¹) h.val⁻¹
    rw [mul_inv_rev, rightAction_mul]

instance latticeSubgroupInverseAction_continuous {n : ℕ} (H : Subgroup (G n)) :
    ContinuousSMul H (X n) where
  continuous_smul := by
    change Continuous (fun p : H × X n => rightAction p.2 (p.1.val)⁻¹)
    exact (continuous_rightAction_uncurry n).comp
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst).inv)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockErgodicity
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# An actual ergodic root flow on a single block component

For a fixed coordinate block, the group generated by its root groups has
the same invariant measurable sets as any one of its nontrivial root
flows.  The Mautner argument proves this for the actual lattice action.
The coordinate block is not required to be the whole ambient space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal Pointwise

namespace DukePrimeDegree
open PrimeDegreePackets

def singleBlockRootGroup {n : ℕ} (S : Set (Fin n)) : Subgroup (G n) :=
  Subgroup.closure {g | ∃ (p q : Fin n) (hpq : p ≠ q) (t : ℝ),
    p ∈ S ∧ q ∈ S ∧ g = Matrix.SpecialLinearGroup.transvection hpq t}

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockNormalization
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
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

attribute [local irreducible] singleBlockRootGroup

def singleBlockDiagonalMean {n : ℕ} (S : Finset (Fin n)) (g : G n) : ℝ :=
  (∑ i ∈ S, Real.log (g.val i i)) / S.card

def singleBlockDiagonalWeights {n : ℕ} (S : Finset (Fin n))
    (g : G n) (i : Fin n) : ℝ :=
  if i ∈ S then singleBlockDiagonalMean S g - Real.log (g.val i i) else 0

lemma singleBlockDiagonalWeights_sum {n : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty) (g : G n) :
    ∑ i, singleBlockDiagonalWeights S g i = 0 := by
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  have hsum : ∑ i, singleBlockDiagonalWeights S g i =
      ∑ i ∈ S, (singleBlockDiagonalMean S g - Real.log (g.val i i)) := by
    simp only [singleBlockDiagonalWeights, Finset.sum_ite_mem, Finset.univ_inter]
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  dsimp only [singleBlockDiagonalMean]
  field_simp [hcard]
  ring

@[irreducible] def singleBlockDiagonalCorrection {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (g : G n) : G n :=
  diagonalOneParameter (singleBlockDiagonalWeights S g)
    (singleBlockDiagonalWeights_sum S hS g) 1

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockCorrectedPairs
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized generic pairs from null block orbits

The small return matrices, their within-block normalizations and the
common compact corrections are selected in this proof. The correction
group is the closure of the single root block, so it preserves the same
component measure. The conclusion does not assume genericity of the
normalized points or a transverse limiting element.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

def singleBlockClosureGroup {n : ℕ} (S : Set (Fin n)) :=
  (singleBlockRootGroup S).topologicalClosure

attribute [local irreducible] singleBlockRootGroup blockMatrixGroup singleBlockClosureGroup

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockShell
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A fixed compact set of transverse shearing limits

Normalizing the selected block makes the within-block part of every
limiting conjugate equal to the identity. A fixed positive displacement
therefore gives a compact set disjoint from the block group. Local
containment of the actual stabilizer in that group supplies a sufficiently
small displacement, before the generic points or the limiting shear are
chosen.
-/

noncomputable section
open Matrix Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def transverseMatrixShell {n : ℕ} (r : Setoid (Fin n)) (a : ℝ) : Set (G n) :=
  {g | withinBlockPart r g.val = 1 ∧ slMatrixDifference g 1 = a}

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CountableWeakKernel
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A probability kernel is measurable for the weak topology

A countable family of finite-basis-union evaluations defines a stronger
second-countable topology on probabilities. Kernel evaluations are measurable
for that topology, and the countable Portmanteau criterion makes the map
to the usual weak topology continuous. No global measurable-space
instance on probabilities is changed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Topology ENNReal

namespace DukePrimeDegree

variable (Y : Type*) [TopologicalSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]

def basisProbabilityTests (p : BasisProbability Y) :
    Finset (countableBasis Y) → ℝ≥0∞ :=
  fun F => (p.toProbability : Measure Y) (finiteBasisUnion F)

instance instTopologicalSpaceBasisProbability : TopologicalSpace (BasisProbability Y) :=
  TopologicalSpace.induced (basisProbabilityTests Y) inferInstance

instance instMeasurableSpaceBasisProbability : MeasurableSpace (BasisProbability Y) := borel (BasisProbability Y)

instance instBorelSpaceBasisProbability : BorelSpace (BasisProbability Y) := ⟨rfl⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FiniteProjectionFrames
attribute [-instance] _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

section Measurability

variable {Z I E : Type*} [MeasurableSpace Z] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Compat: Mathlib d13f23b's Borel structure on `Matrix`. -/
instance compatMatrixBorelSpaceFPF {m n : Type*} [Finite m] [Finite n] :
    BorelSpace (Matrix m n ℝ) :=
  inferInstanceAs (BorelSpace (m → n → ℝ))

end Measurability

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_VelocityTransportRank
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rank transport for actual stabilizer frames

Right translation conjugates the actual velocity space by a linear
equivalence. Thus the cardinality of the constructed measurable frame
is preserved under component-kernel covariance. This supplies the
invariant rank events used by the finite-frame recurrence theorem.
-/

noncomputable section
open MeasureTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets

def slMatrixConjugationEquiv {n : ℕ} (a : G n) :
    Matrix (Fin n) (Fin n) ℝ ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  { slMatrixConjugationLinear a with
    invFun := slMatrixConjugationLinear a⁻¹
    left_inv := fun V => by
      change slMatrixConjugation a⁻¹ (slMatrixConjugation a V) = V
      simpa only [inv_inv] using slMatrixConjugation_inverse a⁻¹ V
    right_inv := fun V => slMatrixConjugation_inverse a V }

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuotientLogDistance
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic displacement distance on the lattice quotient

Taking the infimum over actual right translations gives a distance
independent of a representative. Its triangle inequality and translation
bound provide uniformly controlled real observables on the quotient.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

def rightDisplacementLengths {n : ℕ} (x y : X n) : Set ℝ :=
  {r | ∃ g : G n, rightAction x g=y ∧ matrixLogLength g=r}

def quotientLogDistance {n : ℕ} (x y : X n) : ℝ := sInf (rightDisplacementLengths x y)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_NeutralNameCovers
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable selection of neutral orbit approximations

A finite cover by neutral displacements admits a measurable choice of
reference displacement. The same finite list works for every orbit length.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

local instance instMeasurableSpaceG (n : ℕ) : MeasurableSpace (G n) := borel (G n)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PositiveRootPattern
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix support of groups generated by positive roots

Transitive positive root sets define matrix patterns preserved by all
products of their root generators. The assertion also holds on the
closure, supplying the concrete support restriction for root induction.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma isClosed_positiveRootPattern {n : ℕ} (S : Finset (Fin n × Fin n)) :
    IsClosed {g : G n | PositiveRootPattern S g} := by
  simp only [PositiveRootPattern, Set.ofPred_forall]
  apply isClosed_iInter
  intro r
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro _
  exact isClosed_eq (by fun_prop) continuous_const

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PositiveRootCoordinates
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coordinates separating an extremal root

Multiplication identifies a positive-root group with one real root
coordinate and the group of remaining roots. Both directions are
continuous, and the first coordinate is the corresponding matrix entry.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma transvection_mul_root_entry {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    (t : ℝ) (g : G n) :
    (Matrix.SpecialLinearGroup.transvection hab t * g).val a b =
      g.val a b + t * g.val b b := by
  change ((1 + Matrix.single a b t) * g.val) a b = _
  simp [Matrix.add_mul]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootDisintegration
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Disintegration in the actual upper-root charts

Both the final Gaussian transversal and the finite product of root times
are standard Borel spaces. The open quotient charts therefore give
finite coordinate measures and genuine conditional probability kernels.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

instance specialLinear_standardBorel (n : ℕ) : StandardBorelSpace (G n) := by
  let : PolishSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (PolishSpace (Fin n → Fin n → ℝ))
  have hc : IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.det = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  let : PolishSpace (G n) := hc.polishSpace
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootWindows
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exhausting upper-root time by compactly contained cubes

The ordered real root coordinates give explicit increasing open cubes,
compact closed cubes, and countable families of long quotient boxes.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

instance upperRootTransverse_secondCountable (n : ℕ) :
    SecondCountableTopology (UpperRootTransverse n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootLeafMeasure
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Locally finite conditional measures on complete upper-root leaves

The finite-box conditionals have compatible normalized restrictions.
Their increasing limit is a locally finite measure on all real root
coordinates, uniquely determined by the countable long-box atlas.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma subgroup_free_of_free_translate {n : ℕ} (H : Subgroup (G n)) (x : X n)
    (w : G n) (hw : w ∈ H)
    (hf : ∀ v ∈ H, rightAction (rightAction x w) v = rightAction x w → v = 1) :
    ∀ v ∈ H, rightAction x v = x → v = 1 := by
  intro v hv hfix
  have he : rightAction (rightAction x w) (w⁻¹ * v * w) = rightAction x w := by
    rw [rightAction_mul]
    have hm : w * (w⁻¹ * v * w) = v * w := by group
    rw [hm, ←rightAction_mul, hfix]
  have hh := hf (w⁻¹ * v * w) (H.mul_mem (H.mul_mem (H.inv_mem hw) hv) hw) he
  have heq := congrArg (fun a : G n => w * a * w⁻¹) hh
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_one,
    mul_inv_cancel] using heq

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_NeutralFiberNames
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable reference names on bilateral itinerary fibers -/

noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def bilateralNameFiber {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (x : X n) : Set (X n) :=
  {y | (∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) ∧
    ∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
      Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)}

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_BilateralConditionalSupport
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual conditional measures on bilateral itinerary fibers -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def bilateralNameObservation {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (Q : X n → ℕ)
    (x : X n) : (ℕ → ℕ) × (ℕ → ℕ) :=
  (fun k => Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x),
   fun k => Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_BilateralFiniteCodes
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

def bilateralFiniteCode {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (Q : X n → ℕ)
    (m : ℕ) (x : X n) :
    (Fin m → Fin (m+1)) × (Fin m → Fin (m+1)) :=
  (fun i => heightClip Q m
      ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[i.val] x),
   fun i => heightClip Q m
      ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[i.val] x))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FutureSigmaAlgebra
attribute [-instance] _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

lemma transverseLabelSigma_eq_sup {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]
    {N : ℕ} (Q : S × V → Fin N) :
    transverseLabelSigma Q =
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace S) ⊔ observationSigma Q := by
  exact MeasurableSpace.comap_prodMk Prod.fst Q

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_CountableFutureSigma
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

theorem transverseCountableFutureSigma_eq_sup {S V Y : Type*}
    [MeasurableSpace S] [MeasurableSpace V]
    (T : Y → Y) (Q : Y → ℕ) (F : S × V → Y) :
    (⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z))) =
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace S) ⊔
        MeasurableSpace.comap F (⨆ k : ℕ, observationSigma (fun y => Q (T^[k+1] y))) := by
  simp_rw [transverseLabelSigma_eq_sup,
    show (fun z => countableFutureCode T Q _ (F z)) = countableFutureCode T Q _ ∘ F from rfl,
    observationSigma_comp_eq_comap]
  rw [iSup_sup_eq,iSup_const,←MeasurableSpace.comap_iSup,countableFutureCode_sigma_generate]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_CountableFutureMap
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

lemma transverseCountableFutureSigma_eq_comap {S V Y : Type*}
    [MeasurableSpace S] [MeasurableSpace V]
    (T : Y → Y) (Q : Y → ℕ) (F : S × V → Y) :
    (⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z))) =
      MeasurableSpace.comap (fun z => (z.1, entireFutureObservation T Q (F z)))
        (inferInstance : MeasurableSpace (S × (ℕ → ℕ))) := by
  rw [transverseCountableFutureSigma_eq_sup]
  calc
    _ = MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace S) ⊔
        MeasurableSpace.comap (entireFutureObservation T Q ∘ F)
          (inferInstance : MeasurableSpace (ℕ → ℕ)) := by
      rw [countableFutureSigma_eq_comap, MeasurableSpace.comap_comp]
    _ = _ := (MeasurableSpace.comap_prodMk
      (Prod.fst : S × V → S) (entireFutureObservation T Q ∘ F)).symm

/-- Fiber masses of a kernel depending only on the transverse coordinate
are measurable in the transverse-future sigma algebra itself. Thus mass
conditions used to select boxes really are future events. -/
theorem measurable_countableFuture_mass {S V Y : Type*}
    [MeasurableSpace S] [MeasurableSpace V] [MeasurableSpace Y]
    (κ : Kernel S V) [IsSFiniteKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F)
    (A : Set (S × V)) (hA : MeasurableSet A) :
    Measurable[⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z))]
      (fun z => κ z.1 ({t | (z.1,t) ∈ A} ∩ countableFutureFiber T Q F z)) := by
  let q := entireFutureObservation T Q
  have hq : Measurable q := entireFutureObservation_measurable hT hQ
  have hrel : MeasurableSet {p : (S × (ℕ → ℕ)) × V |
      (p.1.1,p.2) ∈ A ∧ q (F (p.1.1,p.2)) = p.1.2} :=
    (hA.preimage (measurable_fst.fst.prodMk measurable_snd)).inter
      (measurableSet_eq_fun
        (hq.comp (hF.comp (measurable_fst.fst.prodMk measurable_snd))) measurable_fst.snd)
  have H : Measurable (fun b : S × (ℕ → ℕ) =>
      κ b.1 {t | (b.1,t) ∈ A ∧ q (F (b.1,t)) = b.2}) :=
    Kernel.measurable_kernel_prodMk_left (κ := κ.prodMkRight (ℕ → ℕ)) hrel
  have hη : Measurable[⨆ m, transverseLabelSigma
      (fun z => countableFutureCode T Q m (F z))]
      (fun z => (z.1,q (F z))) := by
    rw [transverseCountableFutureSigma_eq_comap]
    exact comap_measurable _
  convert H.comp hη using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  congr 1
  ext t
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, countableFutureFiber,
    q, entireFutureObservation, funext_iff]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FutureFiberKernel
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local future conditional as a self-consistent Markov kernel -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable {S V Y : Type*} [MeasurableSpace S] [MeasurableSpace V] [MeasurableSpace Y]

def futureSliceKernel (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) : Kernel (S × V) V where
  toFun z := (κ z.1).restrict (countableFutureFiber T Q F z)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    simp only [Measure.restrict_apply hA]
    have h := measurable_countableFuture_mass κ hT hQ hF
      (Prod.snd ⁻¹' A) (hA.preimage measurable_snd)
    have hm : (⨆ m, transverseLabelSigma
        (fun z => countableFutureCode T Q m (F z))) ≤
        (inferInstance : MeasurableSpace (S × V)) := by
      apply iSup_le
      intro m
      exact (measurable_fst.prodMk ((countableFutureCode_measurable hT hQ m).comp hF)).comap_le
    exact h.mono hm le_rfl

def normalizedFutureSliceKernel (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) : Kernel (S × V) V where
  toFun z :=
    ((futureSliceKernel κ hT hQ hF z) univ)⁻¹ • futureSliceKernel κ hT hQ hF z
  measurable' := by
    let ν := futureSliceKernel κ hT hQ hF
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    change Measurable (fun z => (ν z univ)⁻¹ * ν z A)
    exact (ν.measurable_coe MeasurableSet.univ).inv.mul (ν.measurable_coe hA)

def futureFiberTimeKernel (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) : Kernel (S × V) V :=
  let ν := futureSliceKernel κ hT hQ hF
  Kernel.piecewise
    (measurableSet_eq_fun (g := fun _ => (0 : ℝ≥0∞))
      (ν.measurable_coe MeasurableSet.univ) measurable_const).compl
    (normalizedFutureSliceKernel κ hT hQ hF)
    (Kernel.deterministic Prod.snd measurable_snd)

def futureFiberCoordinateKernel (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) : Kernel (S × V) (S × V) :=
  (Kernel.deterministic Prod.fst measurable_fst).prod (futureFiberTimeKernel κ hT hQ hF)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuotientLiftMeasure
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lifting an arbitrary finite measure through the arithmetic covering

The countable sum over deck transformations restricts on every injective
chart to the original quotient measure. In particular this construction
applies also to singular invariant measures.
-/

noncomputable section
open MeasureTheory Set Function TopologicalSpace
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

def quotientLiftMeasure (n : ℕ) (μ : Measure (X n)) (s : X n → G n) : Measure (G n) :=
  Measure.sum (fun γ : integralGroup n => μ.map (fun x => γ.val*s x))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ShiftedRootPullback
attribute [-instance] _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

def shiftedRootFactorCoordinateMap {n : ℕ} {a b k : Fin n}
    (e : T × B → RootSlice a b k) (τ : T × B → ℝ) :
    (T × B) × ℝ → RootSlice a b k × ℝ := fun z => (e z.1,z.2 + τ z.1)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_WeylReindex
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

lemma reindexSpecialLinear_integral {n : ℕ} (e : Equiv.Perm (Fin n))
    {g : G n} (hg : g ∈ integralGroup n) :
    reindexSpecialLinear ℝ e g ∈ integralGroup n := by
  obtain ⟨a, rfl⟩ := hg
  refine ⟨reindexSpecialLinear ℤ e a, ?_⟩
  apply Subtype.ext
  rfl

def quotientReindex {n : ℕ} (e : Equiv.Perm (Fin n)) : X n → X n :=
  Quotient.map (reindexSpecialLinear ℝ e) (by
    intro a b hab
    change (QuotientGroup.rightRel (integralGroup n)) a b at hab
    change (QuotientGroup.rightRel (integralGroup n))
      (reindexSpecialLinear ℝ e a) (reindexSpecialLinear ℝ e b)
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa only [map_mul, map_inv] using reindexSpecialLinear_integral e hab)

lemma quotientReindex_symm_apply {n : ℕ} (e : Equiv.Perm (Fin n)) (x : X n) :
    quotientReindex e.symm (quotientReindex e x) = x := by
  induction x using Quotient.inductionOn with
  | h a =>
    change Quotient.mk _ ((reindexSpecialLinear ℝ e).symm (reindexSpecialLinear ℝ e a)) =
      Quotient.mk _ a
    rw [MulEquiv.symm_apply_apply]

lemma continuous_quotientReindex {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Continuous (quotientReindex e) := by
  apply continuous_quot_lift
  exact continuous_quotient_mk'.comp (continuous_reindexSpecialLinear e)

def quotientReindexHomeomorph {n : ℕ} (e : Equiv.Perm (Fin n)) : X n ≃ₜ X n where
  toFun := quotientReindex e
  invFun := quotientReindex e.symm
  left_inv := quotientReindex_symm_apply e
  right_inv x := by simpa only [Equiv.symm_symm] using quotientReindex_symm_apply e.symm x
  continuous_toFun := continuous_quotientReindex e
  continuous_invFun := continuous_quotientReindex e.symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_WeylDiagonalAction
attribute [-instance] _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diagonal invariance and ergodicity under coordinate permutations -/

noncomputable section
open MeasureTheory Set Filter
namespace DukePrimeDegree
open PrimeDegreePackets

/-- The original last coordinate is restored before the coordinates are permuted. -/
def reindexLogCoordinates (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (u : LogCoordinates d) : LogCoordinates d :=
  fun i => restoredLogCoordinates u (e.symm i.castSucc)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_WeylRootBoxes
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing actual root boxes without changing the root parameter

A coordinate permutation carries the pivot, transverse slice, and quotient
root box to their permuted versions.  The real root coordinate is unchanged,
so disintegration transports the conditional measure without a rescaling.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rootSliceReindexHomeomorph {n : ℕ} (e : Equiv.Perm (Fin n))
    (i j k : Fin n) : RootSlice i j k ≃ₜ RootSlice (e i) (e j) (e k) where
  toFun s := ⟨reindexSpecialLinear ℝ e s.val, by
    change s.val.val (e.symm (e k)) (e.symm (e i)) ≠ 0 ∧
      s.val.val (e.symm (e k)) (e.symm (e j)) = 0
    simpa only [e.symm_apply_apply] using s.prop⟩
  invFun s := ⟨reindexSpecialLinear ℝ e.symm s.val, by
    change s.val.val (e k) (e i) ≠ 0 ∧ s.val.val (e k) (e j) = 0
    exact s.prop⟩
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    ext a b
    change s.val.val (e.symm (e a)) (e.symm (e b)) = s.val.val a b
    rw [e.symm_apply_apply, e.symm_apply_apply]
  right_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    ext a b
    change s.val.val (e (e.symm a)) (e (e.symm b)) = s.val.val a b
    rw [e.apply_symm_apply, e.apply_symm_apply]
  continuous_toFun := ((continuous_reindexSpecialLinear e).comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_reindexSpecialLinear e.symm).comp
    continuous_subtype_val).subtype_mk _

def rootReindexCoordinates {n : ℕ} (e : Equiv.Perm (Fin n)) (i j k : Fin n) :
    (RootSlice i j k × ℝ) ≃ₜ (RootSlice (e i) (e j) (e k) × ℝ) :=
  (rootSliceReindexHomeomorph e i j k).prodCongr (Homeomorph.refl ℝ)

end DukePrimeDegree

end

end OAI
end


