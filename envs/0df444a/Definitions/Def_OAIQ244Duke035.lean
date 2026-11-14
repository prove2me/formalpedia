-- Prove2me | Definitions.Def_OAIQ244Duke035
-- name    : OAIQ244Duke035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:40:00.241222+00:00
-- url     : https://prove2.me/theorems/e0bcd25e-6b25-48ab-9763-d5dbb6f454d8
-- title:
--   Definitions bundle OAIQ244Duke035 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 185 declarations of OpenAI's Lean: 54 definitions, 2 inductive types or structures, 7 instances and 122 theorems. The definitions and types are `OAI.DukePrimeDegree.PositiveTransverse`, `OAI.DukePrimeDegree.RootBox.reindex`, `OAI.DukePrimeDegree.RootBox.translate`, `OAI.DukePrimeDegree.RootLeafRegular`, `OAI.DukePrimeDegree.RootPairLeafCovariance`, `OAI.DukePrimeDegree.RootPairSelectionData`, `OAI.DukePrimeDegree.RootPrefixBox`, `OAI.DukePrimeDegree.RootPrefixBox.IsNormalizedPrefixLeaf`, `OAI.DukePrimeDegree.RootPrefixBox.basedLeaf`, `OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel`, `OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure`, `OAI.DukePrimeDegree.RootPrefixBox.domain`, `OAI.DukePrimeDegree.RootPrefixBox.intrinsicProductConditional`, `OAI.DukePrimeDegree.RootPrefixBox.leafKernel`, `OAI.DukePrimeDegree.RootPrefixBox.leafMeasure`, `OAI.DukePrimeDegree.RootPrefixBox.param`, `OAI.DukePrimeDegree.RootPrefixBox.range`, `OAI.DukePrimeDegree.RootPrefixBox.regularLeafKernel`, `OAI.DukePrimeDegree.RootPrefixBox.shrink`, `OAI.DukePrimeDegree.RootPrefixBox.uncenteredIntrinsicProduct`, `OAI.DukePrimeDegree.RootPrefixCoordinates.empty`, `OAI.DukePrimeDegree.RootPrefixCoordinates.groupParam`, `OAI.DukePrimeDegree.RootPrefixCoordinates.longBoxFamily`, `OAI.DukePrimeDegree.RootPrefixCoordinates.nextTimeCoordinates`, `OAI.DukePrimeDegree.RootPrefixCoordinates.nextTimeFiber`, `OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixCoordinates`, `OAI.DukePrimeDegree.RootPrefixCoordinates.prefixTimeExchange`, `OAI.DukePrimeDegree.RootPrefixCoordinates.quotientParam`, `OAI.DukePrimeDegree.RootPrefixCoordinates.rectangleBasePoint`, `OAI.DukePrimeDegree.RootPrefixCoordinates.remainingFactorTime`, `OAI.DukePrimeDegree.RootPrefixCoordinates.timeGroupParam`, `OAI.DukePrimeDegree.RootPrefixCoordinates.timeParam`, `OAI.DukePrimeDegree.RootPrefixCoordinates.unrestrictedPrefixBasePoint`, `OAI.DukePrimeDegree.RootPrefixCoordinates.wholeFutureBoxFamily`, `OAI.DukePrimeDegree.finiteRemainingCubes`, `OAI.DukePrimeDegree.intrinsicLeafData`, `OAI.DukePrimeDegree.locallyFiniteRemainingVersion`, `OAI.DukePrimeDegree.neutralEmptyPrefix`, `OAI.DukePrimeDegree.neutralProductParam`, `OAI.DukePrimeDegree.neutralQuotientParam` and 16 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `DukePrimeDegree_Dynamics_LeafFlowCovariance`, `DukePrimeDegree_Dynamics_ShearingSelectionData`, `DukePrimeDegree_Entropy_WholeFutureCountableCover`, `DukePrimeDegree_Geometry_CompactPhysicalRectangles`, `DukePrimeDegree_Geometry_FactorPivotCylinder`, `DukePrimeDegree_Geometry_FactorSliceFreeness`, `DukePrimeDegree_Geometry_LeafLusin`, `DukePrimeDegree_Geometry_NeutralCoordinateMeasure`, `DukePrimeDegree_Geometry_NeutralPatchNull`, `DukePrimeDegree_Geometry_NeutralPrefixMap`, `DukePrimeDegree_Geometry_NeutralTransverseCoordinates`, `DukePrimeDegree_Geometry_NeutralUpperRootChart`, `DukePrimeDegree_Geometry_PhysicalPrefixCoordinates`, `DukePrimeDegree_Geometry_PhysicalPrefixMeasure`, `DukePrimeDegree_Geometry_PhysicalRootEmbeddings`, `DukePrimeDegree_Geometry_PhysicalRootRectangles`, `DukePrimeDegree_Geometry_PositiveRootCoordinates`, `DukePrimeDegree_Geometry_PrefixRegionFibers`, `DukePrimeDegree_Geometry_PrefixTimeExchange`, `DukePrimeDegree_Geometry_RegularLusinSets`, `DukePrimeDegree_Geometry_RemainingRootProductBoxes`, `DukePrimeDegree_Geometry_RootCompactTransversals`, `DukePrimeDegree_Geometry_RootFactorTransversal`, `DukePrimeDegree_Geometry_RootPairTimeSelection`, `DukePrimeDegree_Geometry_RootPrefixBasedMeasure`, `DukePrimeDegree_Geometry_RootPrefixBoxes`, `DukePrimeDegree_Geometry_RootPrefixCompatibility`, `DukePrimeDegree_Geometry_RootPrefixCoordinates`, `DukePrimeDegree_Geometry_RootPrefixFactorChart`, `DukePrimeDegree_Geometry_RootPrefixLeafKernel`, `DukePrimeDegree_Geometry_RootPrefixLeafMeasure`, `DukePrimeDegree_Geometry_RootPrefixLift`, `DukePrimeDegree_Geometry_RootPrefixLongBoxes`, `DukePrimeDegree_Geometry_RootPrefixNormalizedLeaves`, `DukePrimeDegree_Geometry_RootPrefixProductKernel`, `DukePrimeDegree_Geometry_RootPrefixRegularKernel`, `DukePrimeDegree_Geometry_RootPrefixRestrictions`, `DukePrimeDegree_Geometry_RootPrefixSupport`, `DukePrimeDegree_Geometry_RootPrefixWindows`, `DukePrimeDegree_Geometry_RootRectangleMeasures`, `DukePrimeDegree_Geometry_RootTranslateBox`, `DukePrimeDegree_Geometry_ShiftedRootLeafHolonomy`, `DukePrimeDegree_Geometry_ShiftedRootPullback`, `DukePrimeDegree_Geometry_UpperRootDiagonalCharts`, `DukePrimeDegree_Geometry_WeylRootBoxes`, `PrimePackets_ConditionalFibers`, `PrimePackets_IntrinsicLeaves`, `PrimePackets_KernelScaling`, `PrimePackets_LeafAnchors`, `PrimePackets_LeafNormalization`, `PrimePackets_LeafSupport`, `PrimePackets_LeafTransitions`, `PrimePackets_RayDescent`, `PrimePackets_RootCharts`, `PrimePackets_RootLeaves`, `PrimePackets_RootRelations`.
--
--   **Imports.** It imports the published bundle `Def_DukePrimeDegree`; the bundles `OAIQ244Duke021`, `OAIQ244Duke022` and `OAIQ244Duke023` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke044`; the statements `OAI.DukePrimeDegree.RootPrefixBox.ae_conditionalKernel_eq_dirac_of_atomic_roots`, `OAI.DukePrimeDegree.RootPrefixBox.ae_normalized_uncentered_eq_regularLeaf`, `OAI.DukePrimeDegree.RootPrefixBox.selfConstant_image_massContained`, `OAI.DukePrimeDegree.exists_compact_equal_leaf_shearing_sequence` and `OAI.DukePrimeDegree.nonempty_rootPairSelectionData`; the proofs of `OAI.DukePrimeDegree.RootPrefixBox.selfConstant_image_massContained`, `OAI.DukePrimeDegree.RootPrefixCoordinates.predecessor_entropyRate_le_root_information_add_auxiliary`, `OAI.DukePrimeDegree.RootPrefixCoordinates.wholeFutureKernel_stationary`, `OAI.DukePrimeDegree.eklPrimeInput_unconditional` and `OAI.DukePrimeDegree.root_invariant_of_atomic_companion_leaves`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Piecewise
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke021
import Definitions.Def_OAIQ244Duke022
import Definitions.Def_OAIQ244Duke023

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootRelations
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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
namespace PrimeDegreePackets

lemma rootPivotHomeomorph_translate {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (g : RootPivot i k) (t : ℝ) :
    rootPivotHomeomorph hij (rootPivotTranslate hij g t) =
      ((rootPivotHomeomorph hij g).1,(rootPivotHomeomorph hij g).2+t) := by
  exact Prod.ext (rootSliceRepresentative_translate hij g t) (rootParameter_translate hij g t)

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootCharts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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
namespace PrimeDegreePackets

lemma rootQuotientParametrization_add {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (s : RootSlice i j k) (a t : ℝ) :
    rootQuotientParametrization hij (s,a+t) =
      rightAction (rootQuotientParametrization hij (s,a))
        (Matrix.SpecialLinearGroup.transvection hij t) := by
  change Quotient.mk _ (s.val * Matrix.SpecialLinearGroup.transvection hij (a+t)) =
    Quotient.mk _ ((s.val * Matrix.SpecialLinearGroup.transvection hij a) *
      Matrix.SpecialLinearGroup.transvection hij t)
  rw [Matrix.SpecialLinearGroup.transvection_add,mul_assoc]

end PrimeDegreePackets


namespace PrimeDegreePackets

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma map_coordinateMeasure (B : RootBox hij k) (μ : Measure (X n)) :
    Measure.map (rootQuotientParametrization hij) (B.coordinateMeasure μ) =
      μ.restrict B.range := by
  rw [coordinateMeasure,Measure.map_map]
  · exact B.embedding.measurableEmbedding.map_comap μ
  · exact (rootQuotientParametrization_localHomeomorph hij).continuous.measurable
  · exact measurable_subtype_coe

instance conditionalKernel_markov (B : RootBox hij k) (μ : Measure (X n))
    [IsFiniteMeasure μ] : IsMarkovKernel (B.conditionalKernel μ) := by
  unfold conditionalKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)



end RootBox

end PrimeDegreePackets


namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma coordinateMeasure_ae_domain (B : RootBox hij k) (μ : Measure (X n)) :
    ∀ᵐ z ∂B.coordinateMeasure μ, z ∈ B.domain := by
  rw [coordinateMeasure]
  exact (ae_map_iff measurable_subtype_coe.aemeasurable
    (B.transverse_open.prod B.time_open).measurableSet).mpr
      (ae_of_all _ fun z => z.prop)

lemma coordinateMeasure_fst_ae_transverse (B : RootBox hij k) (μ : Measure (X n)) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst, s ∈ B.transverse := by
  rw [Measure.fst]
  apply (ae_map_iff measurable_fst.aemeasurable B.transverse_open.measurableSet).mpr
  filter_upwards [B.coordinateMeasure_ae_domain μ] with z hz
  exact hz.1

 

lemma conditionalKernel_ae_time (B : RootBox hij k) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst, ∀ᵐ t ∂B.conditionalKernel μ s, t ∈ B.time := by
  have H : ∀ᵐ z ∂((B.coordinateMeasure μ).fst ⊗ₘ B.conditionalKernel μ), z.2 ∈ B.time := by
    rw [conditionalKernel,Measure.disintegrate]
    filter_upwards [B.coordinateMeasure_ae_domain μ] with z hz
    exact hz.2
  exact Measure.ae_ae_of_ae_compProd H

lemma conditionalKernel_time_mass (B : RootBox hij k) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst, B.conditionalKernel μ s B.time = 1 := by
  filter_upwards [B.conditionalKernel_ae_time μ] with s hs
  rw [← measure_univ (μ := B.conditionalKernel μ s)]
  exact measure_congr (ae_eq_univ.mpr hs)

 

lemma coordinateMeasure_apply (B : RootBox hij k) (μ : Measure (X n))
    {S : Set (RootSlice i j k × ℝ)} (hS : MeasurableSet S) :
    B.coordinateMeasure μ S =
      μ (rootQuotientParametrization hij '' (S ∩ B.domain)) := by
  rw [coordinateMeasure,Measure.map_apply measurable_subtype_coe hS,
    B.embedding.measurableEmbedding.comap_apply]
  congr 1
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z.val,⟨hz,z.prop⟩,rfl⟩
  · rintro ⟨z,⟨hz,hzd⟩,rfl⟩
    exact ⟨⟨z,hzd⟩,hz,rfl⟩



end PrimeDegreePackets.RootBox

open scoped ENNReal ProbabilityTheory
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_KernelScaling
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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


namespace PrimeDegreePackets.RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}



theorem shrink_coordinateMeasure (B : RootBox hij k)
    (U : Set (RootSlice i j k)) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V)
    (hUB : U ⊆ B.transverse) (hVB : V ⊆ B.time) (μ : Measure (X n)) :
    (B.shrink U V hU hV hUB hVB).coordinateMeasure μ =
      (B.coordinateMeasure μ).restrict (U ×ˢ V) := by
  ext S hS
  rw [Measure.restrict_apply hS,coordinateMeasure_apply _ μ hS,
    coordinateMeasure_apply _ μ (hS.inter (hU.measurableSet.prod hV.measurableSet))]
  congr 2
  change S ∩ U ×ˢ V = (S ∩ U ×ˢ V) ∩ B.domain
  exact (Set.inter_eq_left.mpr ((Set.inter_subset_right).trans (Set.prod_mono hUB hVB))).symm

 

theorem shrink_conditionalKernel (B : RootBox hij k)
    (U : Set (RootSlice i j k)) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V)
    (hUB : U ⊆ B.transverse) (hVB : V ⊆ B.time) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst.restrict U,
      B.conditionalKernel μ s V •
        (B.shrink U V hU hV hUB hVB).conditionalKernel μ s =
          (B.conditionalKernel μ s).restrict V := by
  simp only [conditionalKernel,shrink_coordinateMeasure]
  exact restricted_conditional_kernel _ hU.measurableSet hV.measurableSet

 

theorem shrink_marginal (B : RootBox hij k)
    (U : Set (RootSlice i j k)) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V)
    (hUB : U ⊆ B.transverse) (hVB : V ⊆ B.time) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ((B.shrink U V hU hV hUB hVB).coordinateMeasure μ).fst =
      ((B.coordinateMeasure μ).fst.restrict U).withDensity
        (fun s => B.conditionalKernel μ s V) := by
  rw [shrink_coordinateMeasure,restricted_conditional_marginal _ hU.measurableSet hV.measurableSet]
  rfl

end PrimeDegreePackets.RootBox


open Set Filter Topology

open Set Filter Topology MeasureTheory
namespace PrimeDegreePackets

lemma root_time_injective_of_free {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (s : RootSlice i j k) (a : ℝ)
    (hfree : ∀ v : ℝ,
      rightAction (rootQuotientParametrization hij (s,a))
        (Matrix.SpecialLinearGroup.transvection hij v) =
          rootQuotientParametrization hij (s,a) → v = 0) :
    Function.Injective (fun t : ℝ => rootQuotientParametrization hij (s,t)) := by
  intro t u heq
  have H := congrArg (fun x => rightAction x
    (Matrix.SpecialLinearGroup.transvection hij (a-u))) heq
  rw [←rootQuotientParametrization_add hij s t (a-u),
    ←rootQuotientParametrization_add hij s u (a-u)] at H
  have ht : t+(a-u)=a+(t-u) := by ring
  have hu : u+(a-u)=a := by ring
  rw [ht,hu,rootQuotientParametrization_add hij s a (t-u)] at H
  exact sub_eq_zero.mp (hfree (t-u) H)



end PrimeDegreePackets

open MeasureTheory Set Filter Topology

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafNormalization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
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
namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma shrink_marginal_absolutelyContinuous (B : RootBox hij k)
    (U : Set (RootSlice i j k)) (J : Set ℝ) (hU : IsOpen U) (hJ : IsOpen J)
    (hUB : U ⊆ B.transverse) (hJB : J ⊆ B.time) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ((B.shrink U J hU hJ hUB hJB).coordinateMeasure μ).fst ≪
      (B.coordinateMeasure μ).fst.restrict U := by
  rw [shrink_marginal]
  exact withDensity_absolutelyContinuous _ _

lemma shrink_marginal_ae_anchor_pos (B : RootBox hij k)
    (U : Set (RootSlice i j k)) (J : Set ℝ) (hU : IsOpen U) (hJ : IsOpen J)
    (hUB : U ⊆ B.transverse) (hJB : J ⊆ B.time) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂((B.shrink U J hU hJ hUB hJB).coordinateMeasure μ).fst,
      B.conditionalKernel μ s J ≠ 0 := by
  rw [shrink_marginal]
  exact (ae_withDensity_iff (B.conditionalKernel μ |>.measurable_coe hJ.measurableSet)).mpr
    (ae_of_all _ fun _ h => h)

 

theorem overlap_anchorNormalize (B C : RootBox hij k)
    (U : Set (RootSlice i j k)) (J : Set ℝ) (hU : IsOpen U) (hJ : IsOpen J)
    (hUB : U ⊆ B.transverse) (hUC : U ⊆ C.transverse)
    (hJB : J ⊆ B.time) (hJC : J ⊆ C.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂((B.shrink U J hU hJ hUB hJB).coordinateMeasure μ).fst,
      B.conditionalKernel μ s J ≠ 0 ∧ C.conditionalKernel μ s J ≠ 0 ∧
      (anchorNormalize (B.conditionalKernel μ s) J).restrict (B.time ∩ C.time) =
        (anchorNormalize (C.conditionalKernel μ s) J).restrict (B.time ∩ C.time) := by
  let V := B.time ∩ C.time
  have hV : IsOpen V := B.time_open.inter C.time_open
  let D := B.shrink U V hU hV hUB inter_subset_left
  have hD : D = C.shrink U V hU hV hUC inter_subset_right := rfl
  have hA : B.shrink U J hU hJ hUB hJB = C.shrink U J hU hJ hUC hJC := rfl
  have hB := (B.shrink_marginal_absolutelyContinuous U J hU hJ hUB hJB μ).ae_le
    (B.shrink_conditionalKernel U V hU hV hUB inter_subset_left μ)
  have hC := (C.shrink_marginal_absolutelyContinuous U J hU hJ hUC hJC μ).ae_le
    (C.shrink_conditionalKernel U V hU hV hUC inter_subset_right μ)
  rw [←hA] at hC
  have hpB := B.shrink_marginal_ae_anchor_pos U J hU hJ hUB hJB μ
  have hpC := C.shrink_marginal_ae_anchor_pos U J hU hJ hUC hJC μ
  rw [←hA] at hpC
  filter_upwards [hB,hC,hpB,hpC] with s hsB hsC hpB hpC
  have hJV : J ⊆ V := subset_inter hJB hJC
  have H₁ := (anchorNormalize_restrict _ _ hJ.measurableSet hJV hsB hpB).2
  have H₂ := (anchorNormalize_restrict _ _ hJ.measurableSet hJV hsC hpC).2
  refine ⟨hpB,hpC,?_⟩
  exact H₁.symm.trans H₂


end PrimeDegreePackets.RootBox

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
namespace PrimeDegreePackets

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem ae_injective_root_slice_of_ae_free (B : RootBox hij k)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      Function.Injective (fun t : ℝ => rootQuotientParametrization hij (s,t)) := by
  have hf : ∀ᵐ z ∂B.coordinateMeasure μ, ∀ v : ℝ,
      rightAction (rootQuotientParametrization hij z)
        (Matrix.SpecialLinearGroup.transvection hij v) = rootQuotientParametrization hij z →
          v = 0 := by
    apply ae_of_ae_map (μ := B.coordinateMeasure μ)
      (f := rootQuotientParametrization (k := k) hij)
      (p := fun x => ∀ v : ℝ,
        rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
      (rootQuotientParametrization_localHomeomorph hij).continuous.measurable.aemeasurable
    rw [B.map_coordinateMeasure]
    exact ae_restrict_of_ae hfree
  rw [←Measure.disintegrate (B.coordinateMeasure μ) (B.coordinateMeasure μ).condKernel] at hf
  have H := Measure.ae_ae_of_ae_compProd hf
  filter_upwards [H] with s hs
  obtain ⟨t,ht⟩ := hs.exists
  exact root_time_injective_of_free hij s t ht



lemma shrink_full_time_marginal (B : RootBox hij k)
    (U : Set (RootSlice i j k)) (hU : IsOpen U) (hUB : U ⊆ B.transverse)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ((B.shrink U B.time hU B.time_open hUB subset_rfl).coordinateMeasure μ).fst =
      (B.coordinateMeasure μ).fst.restrict U := by
  rw [shrink_marginal]
  calc
    _ = ((B.coordinateMeasure μ).fst.restrict U).withDensity 1 := by
      apply withDensity_congr_ae
      exact ae_restrict_of_ae (B.conditionalKernel_time_mass μ)
    _ = _ := withDensity_one

end RootBox
end PrimeDegreePackets


namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem base_overlap_anchorNormalize (A B C : RootBox hij k)
    (hAB : A.time ⊆ B.time) (hAC : A.time ⊆ C.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      s ∈ B.transverse → s ∈ C.transverse →
      B.conditionalKernel μ s A.time ≠ 0 ∧ C.conditionalKernel μ s A.time ≠ 0 ∧
      (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (B.time ∩ C.time) =
        (anchorNormalize (C.conditionalKernel μ s) A.time).restrict (B.time ∩ C.time) := by
  let U := A.transverse ∩ B.transverse ∩ C.transverse
  have hU : IsOpen U := (A.transverse_open.inter B.transverse_open).inter C.transverse_open
  have hUA : U ⊆ A.transverse := inter_subset_left.trans inter_subset_left
  have hUB : U ⊆ B.transverse := inter_subset_left.trans inter_subset_right
  have hUC : U ⊆ C.transverse := inter_subset_right
  have H := overlap_anchorNormalize B C U A.time hU A.time_open hUB hUC hAB hAC μ
  have hD : B.shrink U A.time hU A.time_open hUB hAB =
      A.shrink U A.time hU A.time_open hUA subset_rfl := rfl
  rw [hD,A.shrink_full_time_marginal] at H
  have H' := (ae_restrict_iff' hU.measurableSet).mp H
  filter_upwards [H',A.coordinateMeasure_fst_ae_transverse μ] with s hs hsA
  intro hsB hsC
  exact hs ⟨⟨hsA,hsB⟩,hsC⟩

 

theorem base_anchor_restrict (A B : RootBox hij k) (hAB : A.time ⊆ B.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ B.transverse →
      B.conditionalKernel μ s A.time ≠ 0 ∧
      (anchorNormalize (B.conditionalKernel μ s) A.time).restrict A.time =
        A.conditionalKernel μ s := by
  filter_upwards [base_overlap_anchorNormalize A A B subset_rfl hAB μ,
    A.coordinateMeasure_fst_ae_transverse μ,A.conditionalKernel_time_mass μ,
    A.conditionalKernel_ae_time μ] with s hs hsA hm ht
  intro hsB
  have H := hs hsA hsB
  refine ⟨H.2.1,?_⟩
  rw [inter_eq_left.mpr hAB] at H
  rw [←H.2.2]
  have hn : anchorNormalize (A.conditionalKernel μ s) A.time = A.conditionalKernel μ s := by
    simp only [anchorNormalize,hm,inv_one,one_smul]
  rw [hn]
  exact Measure.restrict_eq_self_of_ae_mem ht


end PrimeDegreePackets.RootBox


namespace PrimeDegreePackets


variable {n : ℕ} {i j k : Fin n}


lemma rootLongBoxFamily_countable (hij : i ≠ j) (k : Fin n) (R : ℝ) (m : ℕ) :
    (rootLongBoxFamily hij k R m).Countable :=
  (exists_countable_rootBoxes_exact_time (k := k) hij (-(R+m)) (R+m)).choose_spec.1

lemma rootLongBoxFamily_time (hij : i ≠ j) (k : Fin n) (R : ℝ) (m : ℕ)
    (B : RootBox hij k) (hB : B ∈ rootLongBoxFamily hij k R m) :
    B.time = rootLeafWindow R m :=
  (exists_countable_rootBoxes_exact_time (k := k) hij (-(R+m)) (R+m)).choose_spec.2.1 B hB

lemma rootLongBoxFamily_covers (hij : i ≠ j) (k : Fin n) (R : ℝ) (m : ℕ)
    (s : RootSlice i j k)
    (hs : Function.Injective (fun t : ℝ => rootQuotientParametrization hij (s,t))) :
    ∃ B ∈ rootLongBoxFamily hij k R m, s ∈ B.transverse :=
  (exists_countable_rootBoxes_exact_time (k := k) hij (-(R+m)) (R+m)).choose_spec.2.2 s hs

end PrimeDegreePackets


namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem ae_exists_rootLeafMeasure (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∃ ν : Measure ℝ,
      IsLocallyFiniteMeasure ν ∧ ν A.time = 1 ∧
      ν.restrict A.time = A.conditionalKernel μ s ∧
      ∀ (m : ℕ) (B : RootBox hij k), B ∈ rootLongBoxFamily hij k R m →
        s ∈ B.transverse →
        ν.restrict (rootLeafWindow R m) =
          (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (rootLeafWindow R m) := by
  let C := rootLongBoxFamily hij k R
  have hCc (m : ℕ) : (C m).Countable := rootLongBoxFamily_countable hij k R m
  let (m : ℕ) : Countable (C m) := (hCc m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have hp : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      ∀ (a b : ℕ) (B : C a) (D : C b), s ∈ B.val.transverse → s ∈ D.val.transverse →
        B.val.conditionalKernel μ s A.time ≠ 0 ∧ D.val.conditionalKernel μ s A.time ≠ 0 ∧
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict (B.val.time ∩ D.val.time) =
          (anchorNormalize (D.val.conditionalKernel μ s) A.time).restrict (B.val.time ∩ D.val.time) := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    apply ae_all_iff.mpr
    intro B
    apply ae_all_iff.mpr
    intro D
    exact base_overlap_anchorNormalize A B.val D.val (hinc a B) (hinc b D) μ
  have ha : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      ∀ (m : ℕ) (B : C m), s ∈ B.val.transverse →
        B.val.conditionalKernel μ s A.time ≠ 0 ∧
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict A.time =
          A.conditionalKernel μ s := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    exact base_anchor_restrict A B.val (hinc m B) μ
  filter_upwards [A.ae_injective_root_slice_of_ae_free μ hfree,hp,ha] with s hs hp ha
  have hcover (m : ℕ) : ∃ B : C m, s ∈ B.val.transverse := by
    obtain ⟨B,hB,hsB⟩ := rootLongBoxFamily_covers hij k R m s hs
    exact ⟨⟨B,hB⟩,hsB⟩
  choose B hB using hcover
  let N (m : ℕ) : Measure ℝ :=
    (anchorNormalize ((B m).val.conditionalKernel μ s) A.time).restrict (rootLeafWindow R m)
  have hpos (m : ℕ) : (B m).val.conditionalKernel μ s A.time ≠ 0 := (ha m (B m) (hB m)).1
  let (m : ℕ) : IsFiniteMeasure (anchorNormalize ((B m).val.conditionalKernel μ s) A.time) :=
    anchorNormalize_finite _ _ (hpos m)
  let (m : ℕ) : IsFiniteMeasure (N m) := by dsimp [N]; infer_instance
  have hc : ∀ a b, a ≤ b → (N b).restrict (rootLeafWindow R a) = N a := by
    intro a b hab
    have H := (hp a b (B a) (B b) (hB a) (hB b)).2.2
    rw [hT a (B a),hT b (B b),inter_eq_left.mpr (rootLeafWindow_mono R hab)] at H
    dsimp [N]
    rw [Measure.restrict_restrict (rootLeafWindow_open R a).measurableSet,
      inter_eq_left.mpr (rootLeafWindow_mono R hab)]
    exact H.symm
  let ν := increasingMeasureLimit N (restrictionChain_monotone N (rootLeafWindow R) hc)
  have hν (m : ℕ) : ν.restrict (rootLeafWindow R m) = N m :=
    increasingMeasureLimit_restrict N (rootLeafWindow R)
      (fun m => (rootLeafWindow_open R m).measurableSet) hc m
  have hνA : ν.restrict A.time = A.conditionalKernel μ s := by
    have H := congrArg (fun ξ : Measure ℝ => ξ.restrict A.time) (hν 0)
    dsimp [N] at H
    rw [Measure.restrict_restrict A.time_open.measurableSet,inter_eq_left.mpr hAR,
      Measure.restrict_restrict A.time_open.measurableSet,inter_eq_left.mpr hAR] at H
    exact H.trans (ha 0 (B 0) (hB 0)).2
  refine ⟨ν,increasingMeasureLimit_locallyFinite N (rootLeafWindow R)
    (rootLeafWindow_open R) (fun m => (rootLeafWindow_open R m).measurableSet)
    (rootLeafWindow_cover R) hc,?_,hνA,?_⟩
  · have H := congrArg (fun ξ : Measure ℝ => ξ univ) hνA
    simpa only [Measure.restrict_apply MeasurableSet.univ,univ_inter,measure_univ] using H
  · intro m D hD hsD
    let D' : C m := ⟨D,hD⟩
    have H := (hp m m (B m) D' (hB m) hsD).2.2
    rw [hT m (B m),hT m D',inter_self] at H
    exact (hν m).trans H



end PrimeDegreePackets.RootBox
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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
namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}


lemma leafMeasure_spec_of_exists (A : RootBox hij k) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : RootSlice i j k)
    (h : ∃ ν, A.IsNormalizedRootLeaf R μ s ν) :
    A.IsNormalizedRootLeaf R μ s (A.leafMeasure R μ s) := by
  simpa only [leafMeasure,dite_eq_left h] using h.choose_spec

 
theorem ae_leafMeasure_spec (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      A.IsNormalizedRootLeaf R μ s (A.leafMeasure R μ s) := by
  filter_upwards [A.ae_exists_rootLeafMeasure R hAR μ hfree] with s hs
  exact A.leafMeasure_spec_of_exists R μ s hs

end PrimeDegreePackets.RootBox


namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem ae_leafMeasure_restrict (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (D : RootBox hij k) (hAD : A.time ⊆ D.time) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ D.transverse →
      D.conditionalKernel μ s A.time ≠ 0 ∧
      (A.leafMeasure R μ s).restrict D.time =
        (anchorNormalize (D.conditionalKernel μ s) A.time).restrict D.time := by
  let C := rootLongBoxFamily hij k R
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have hp : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      ∀ (m : ℕ) (B : C m), s ∈ B.val.transverse → s ∈ D.transverse →
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict (B.val.time ∩ D.time) =
          (anchorNormalize (D.conditionalKernel μ s) A.time).restrict (B.val.time ∩ D.time) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    filter_upwards [base_overlap_anchorNormalize A B.val D (hinc m B) hAD μ] with s hs
    exact fun hB hD => (hs hB hD).2.2
  filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree,
    A.ae_injective_root_slice_of_ae_free μ hfree,hp,base_anchor_restrict A D hAD μ]
      with s hs hi hp ha
  intro hsD
  refine ⟨(ha hsD).1,?_⟩
  apply measure_eq_of_restrictionChain (rootLeafWindow R) (rootLeafWindow_mono R)
    (rootLeafWindow_cover R)
  intro m
  obtain ⟨B,hBC,hsB⟩ := rootLongBoxFamily_covers hij k R m s hi
  let B' : C m := ⟨B,hBC⟩
  have H := hp m B' hsB hsD
  rw [hT m B'] at H
  calc
    ((A.leafMeasure R μ s).restrict D.time).restrict (rootLeafWindow R m) =
        ((A.leafMeasure R μ s).restrict (rootLeafWindow R m)).restrict D.time :=
      Measure.restrict_comm (rootLeafWindow_open R m).measurableSet
    _ = ((anchorNormalize (B.conditionalKernel μ s) A.time).restrict (rootLeafWindow R m)).restrict D.time := by
      rw [hs.2.2.2 m B hBC hsB]
    _ = (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (rootLeafWindow R m ∩ D.time) := by
      rw [Measure.restrict_restrict D.time_open.measurableSet,inter_comm]
    _ = (anchorNormalize (D.conditionalKernel μ s) A.time).restrict (rootLeafWindow R m ∩ D.time) := H
    _ = ((anchorNormalize (D.conditionalKernel μ s) A.time).restrict D.time).restrict (rootLeafWindow R m) :=
      (Measure.restrict_restrict (rootLeafWindow_open R m).measurableSet).symm


end PrimeDegreePackets.RootBox


open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory


namespace PrimeDegreePackets

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

lemma base_ae_of_ae (A B : RootBox hij k) (hAB : A.time ⊆ B.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ] {p : RootSlice i j k → Prop}
    (hp : ∀ᵐ s ∂(B.coordinateMeasure μ).fst, p s) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ B.transverse → p s := by
  let U := A.transverse ∩ B.transverse
  have hU : IsOpen U := A.transverse_open.inter B.transverse_open
  have H := (B.shrink_marginal_absolutelyContinuous U A.time hU A.time_open
    inter_subset_right hAB μ).ae_le (ae_restrict_of_ae hp)
  have hE : B.shrink U A.time hU A.time_open inter_subset_right hAB =
      A.shrink U A.time hU A.time_open inter_subset_left subset_rfl := rfl
  rw [hE,A.shrink_full_time_marginal] at H
  have H' := (ae_restrict_iff' hU.measurableSet).mp H
  filter_upwards [H',A.coordinateMeasure_fst_ae_transverse μ] with s hs hsA
  exact fun hsB => hs ⟨hsA,hsB⟩

end RootBox
end PrimeDegreePackets


namespace PrimeDegreePackets

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma aemeasurable_leafMeasure_restrict_window (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (m : ℕ) :
    AEMeasurable (fun s => (A.leafMeasure R μ s).restrict (rootLeafWindow R m))
      (A.coordinateMeasure μ).fst := by
  let C := rootLongBoxFamily hij k R
  let : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  let U := ⋃ B : C m, B.val.transverse
  have hU : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ U := by
    filter_upwards [A.ae_injective_root_slice_of_ae_free μ hfree] with s hs
    obtain ⟨B,hB,hsB⟩ := rootLongBoxFamily_covers hij k R m s hs
    exact mem_iUnion.mpr ⟨⟨B,hB⟩,hsB⟩
  have H : AEMeasurable (fun s => (A.leafMeasure R μ s).restrict (rootLeafWindow R m))
      ((A.coordinateMeasure μ).fst.restrict U) := by
    apply aemeasurable_iUnion_iff.mpr
    intro B
    have hM : Measurable (fun s =>
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict (rootLeafWindow R m)) := by
      apply Measure.measurable_of_measurable_coe
      intro T hT
      simp only [Measure.restrict_apply hT,anchorNormalize,Measure.smul_apply,smul_eq_mul]
      exact ((B.val.conditionalKernel μ).measurable_coe A.time_open.measurableSet).inv.mul
        ((B.val.conditionalKernel μ).measurable_coe (hT.inter (rootLeafWindow_open R m).measurableSet))
    apply hM.aemeasurable.congr
    change ∀ᵐ s ∂(A.coordinateMeasure μ).fst.restrict B.val.transverse, _
    rw [ae_restrict_iff' B.val.transverse_open.measurableSet]
    filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree] with s hs
    intro hsB
    exact (hs.2.2.2 m B.val B.prop hsB).symm
  simpa only [Measure.restrict_eq_self_of_ae_mem hU] using H

 

theorem aemeasurable_leafMeasure (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    AEMeasurable (A.leafMeasure R μ) (A.coordinateMeasure μ).fst := by
  let W := rootLeafWindow R
  let V := disjointed W
  have hV (m : ℕ) : MeasurableSet (V m) :=
    MeasurableSet.disjointed (fun m => (rootLeafWindow_open R m).measurableSet) m
  have hM (m : ℕ) : AEMeasurable
      (fun s => (A.leafMeasure R μ s).restrict (V m)) (A.coordinateMeasure μ).fst := by
    have H := (measurable_measure_restrict (hV m)).comp_aemeasurable
      (A.aemeasurable_leafMeasure_restrict_window R hAR μ hfree m)
    change AEMeasurable (fun s => ((A.leafMeasure R μ s).restrict (W m)).restrict (V m))
      (A.coordinateMeasure μ).fst at H
    have hVW : V m ∩ W m = V m := inter_eq_left.mpr (disjointed_subset W m)
    simpa only [Measure.restrict_restrict (hV m),hVW] using H
  have hE (s : RootSlice i j k) : A.leafMeasure R μ s =
      Measure.sum (fun m => (A.leafMeasure R μ s).restrict (V m)) := by
    exact measure_eq_sum_disjointed (A.leafMeasure R μ s) W
      (fun m => (rootLeafWindow_open R m).measurableSet) (rootLeafWindow_cover R)
  exact (measurable_measure_sum.comp_aemeasurable (aemeasurable_pi_iff.mpr hM)).congr
    (ae_of_all _ fun s => (hE s).symm)

 

def leafKernel (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    Kernel (RootSlice i j k) ℝ where
  toFun := (A.aemeasurable_leafMeasure R hAR μ hfree).mk (A.leafMeasure R μ)
  measurable' := (A.aemeasurable_leafMeasure R hAR μ hfree).measurable_mk

lemma ae_leafKernel_eq (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      A.leafKernel R hAR μ hfree s = A.leafMeasure R μ s :=
  (A.aemeasurable_leafMeasure R hAR μ hfree).ae_eq_mk.symm

end RootBox
end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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



instance locallyFiniteRealVersion_sFinite {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) : IsSFiniteKernel (locallyFiniteRealVersion κ) := by
  apply isSFiniteKernel_of_finite_exhaustion _ (rootLeafWindow 0)
    (fun m => (rootLeafWindow_open 0 m).measurableSet) (rootLeafWindow_cover 0)
  intro a m
  exact (measure_mono Set.Ioo_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 
def regularLeafKernel (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    Kernel (RootSlice i j k) ℝ := locallyFiniteRealVersion (A.leafKernel R hAR μ hfree)

instance regularLeafKernel_sFinite (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    IsSFiniteKernel (A.regularLeafKernel R hAR μ hfree) := locallyFiniteRealVersion_sFinite _

lemma ae_regularLeafKernel_eq (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      A.regularLeafKernel R hAR μ hfree s = A.leafMeasure R μ s := by
  filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree,A.ae_leafKernel_eq R hAR μ hfree] with s hs he
  have : IsLocallyFiniteMeasure (A.leafKernel R hAR μ hfree s) := he.symm ▸ hs.1
  exact (locallyFiniteRealVersion_eq _ s).trans he

end RootBox
end PrimeDegreePackets


namespace PrimeDegreePackets


namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}


lemma aemeasurable_basedLeaf (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    AEMeasurable (A.basedLeaf R μ) (A.coordinateMeasure μ) := by
  have he : ∀ᵐ z ∂A.coordinateMeasure μ,
      A.regularLeafKernel R hAR μ hfree z.1 = A.leafMeasure R μ z.1 :=
    ae_of_ae_map measurable_fst.aemeasurable (A.ae_regularLeafKernel_eq R hAR μ hfree)
  exact (basedRealKernel (A.regularLeafKernel R hAR μ hfree)).measurable.aemeasurable.congr
    (he.mono fun z hz => congrArg (fun ν => basedRealMeasure ν z.2) hz)



end RootBox
end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafAnchors
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

lemma rootTransition_inverse_mul (γ : G n) (s : RootSliceOverlap i j k l γ) :
    γ⁻¹ * (rootSliceRepresentative hij (rootTransitionPivot γ s)).val =
      s.val.val * Matrix.SpecialLinearGroup.transvection hij (-rootTransitionTime γ s) := by
  change γ⁻¹ * ((γ * s.val.val) * _) = _
  rw [←mul_assoc,inv_mul_cancel_left]
  rfl

def rootTransitionSlice (γ : G n) (s : RootSliceOverlap i j k l γ) :
    RootSliceOverlap i j l k γ⁻¹ :=
  ⟨rootSliceRepresentative hij (rootTransitionPivot γ s),by
    rw [rootTransition_inverse_mul,root_mul_entry,ite_eq_right hij,add_zero]
    exact s.val.prop.1⟩

lemma rootTransitionTime_inverse (γ : G n) (s : RootSliceOverlap i j k l γ) :
    rootTransitionTime γ⁻¹ (rootTransitionSlice hij γ s) = -rootTransitionTime γ s := by
  unfold rootTransitionTime
  change rootParameter i j k (γ⁻¹ * (rootSliceRepresentative hij (rootTransitionPivot γ s)).val) = _
  rw [rootTransition_inverse_mul]
  have H := rootParameter_translate hij (⟨s.val.val,s.val.prop.1⟩ : RootPivot i k)
    (-rootTransitionTime γ s)
  simpa only [rootPivotTranslate,rootParameter,s.val.prop.2,zero_div,zero_add,rootTransitionTime] using H

lemma rootTransitionSlice_inverse (γ : G n) (s : RootSliceOverlap i j k l γ) :
    (rootTransitionSlice hij γ⁻¹ (rootTransitionSlice hij γ s)).val.val = s.val.val := by
  change (γ⁻¹ * (rootSliceRepresentative hij (rootTransitionPivot γ s)).val) *
    Matrix.SpecialLinearGroup.transvection hij
      (-rootTransitionTime γ⁻¹ (rootTransitionSlice hij γ s)) = _
  rw [rootTransition_inverse_mul,rootTransitionTime_inverse,mul_assoc,
    ←Matrix.SpecialLinearGroup.transvection_add,neg_neg,neg_add_cancel,
    Matrix.SpecialLinearGroup.transvection_coeff_zero,mul_one]

lemma continuous_rootTransitionSlice (γ : G n) :
    Continuous (rootTransitionSlice (k := k) (l := l) hij γ) := by
  apply Continuous.subtype_mk
  exact (continuous_rootSliceRepresentative hij).comp (continuous_rootTransitionPivot γ)

 

def rootSliceTransition (γ : G n) :
    RootSliceOverlap i j k l γ ≃ₜ RootSliceOverlap i j l k γ⁻¹ where
  toFun := rootTransitionSlice hij γ
  invFun s := ⟨(rootTransitionSlice hij γ⁻¹ s).val, by
    simpa only [inv_inv] using (rootTransitionSlice hij γ⁻¹ s).prop⟩
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    exact rootTransitionSlice_inverse hij γ s
  right_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [rootTransitionSlice,rootTransitionPivot,rootSliceRepresentative,inv_inv]
      using rootTransitionSlice_inverse hij γ⁻¹ s
  continuous_toFun := continuous_rootTransitionSlice hij γ
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (continuous_rootTransitionSlice (k := l) (l := k) hij γ⁻¹)

lemma rootTransition_reconstruct (γ : G n) (s : RootSliceOverlap i j k l γ) (t : ℝ) :
    (rootTransitionSlice hij γ s).val.val *
        Matrix.SpecialLinearGroup.transvection hij (t + rootTransitionTime γ s) =
      γ * (s.val.val * Matrix.SpecialLinearGroup.transvection hij t) := by
  change ((γ * s.val.val) * Matrix.SpecialLinearGroup.transvection hij (-rootTransitionTime γ s)) *
    Matrix.SpecialLinearGroup.transvection hij (t + rootTransitionTime γ s) = _
  rw [mul_assoc,←Matrix.SpecialLinearGroup.transvection_add]
  have h : -rootTransitionTime γ s + (t + rootTransitionTime γ s) = t := by ring
  rw [h,mul_assoc]

end PrimeDegreePackets


namespace PrimeDegreePackets


def rootTransitionCoordinates {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (γ : G n) :
    (RootSliceOverlap i j k l γ × ℝ) ≃ₜ (RootSliceOverlap i j l k γ⁻¹ × ℝ) :=
  fiberShear (rootSliceTransition hij γ) (rootTransitionTime γ) (continuous_rootTransitionTime γ)

lemma rootTransitionCoordinates_param {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (γ : G n) (hγ : γ ∈ integralGroup n)
    (z : RootSliceOverlap i j k l γ × ℝ) :
    rootQuotientParametrization hij ((rootTransitionCoordinates hij γ z).1.val,
      (rootTransitionCoordinates hij γ z).2) =
      rootQuotientParametrization hij (z.1.val,z.2) := by
  change Quotient.mk _ ((rootTransitionSlice hij γ z.1).val.val *
    Matrix.SpecialLinearGroup.transvection hij (z.2 + rootTransitionTime γ z.1)) =
    Quotient.mk _ (z.1.val.val * Matrix.SpecialLinearGroup.transvection hij z.2)
  rw [rootTransition_reconstruct]
  symm
  apply Quotient.sound
  change (QuotientGroup.rightRel (integralGroup n))
    (z.1.val.val * Matrix.SpecialLinearGroup.transvection hij z.2)
    (γ * (z.1.val.val * Matrix.SpecialLinearGroup.transvection hij z.2))
  rw [QuotientGroup.rightRel_apply,mul_inv_cancel_right]
  exact hγ

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ConditionalFibers
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

abbrev rootOverlapParam (hij : i ≠ j) (γ : G n) : RootSliceOverlap i j k l γ × ℝ → X n :=
  fun z => rootQuotientParametrization hij (z.1.val,z.2)

namespace RootBox

abbrev overlapDomain (A : RootBox hij k) (γ : G n) (l : Fin n) :
    Set (RootSliceOverlap i j k l γ × ℝ) :=
  baseSubtypeMap {s : RootSlice i j k | (γ * s.val).1 l i ≠ 0} ⁻¹' A.domain

def overlapMeasure (A : RootBox hij k) (γ : G n) (l : Fin n) (μ : Measure (X n)) :
    Measure (RootSliceOverlap i j k l γ × ℝ) :=
  (A.coordinateMeasure μ).comap (baseSubtypeMap {s : RootSlice i j k | (γ * s.val).1 l i ≠ 0})

instance overlapMeasure_finite (A : RootBox hij k) (γ : G n) (l : Fin n)
    (μ : Measure (X n)) [IsFiniteMeasure μ] : IsFiniteMeasure (A.overlapMeasure γ l μ) := by
  unfold overlapMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma overlapDomain_open (A : RootBox hij k) (γ : G n) (l : Fin n) :
    IsOpen (A.overlapDomain γ l) :=
  (A.transverse_open.prod A.time_open).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

lemma overlapMeasure_apply (A : RootBox hij k) (γ : G n) (l : Fin n)
    (μ : Measure (X n)) {S : Set (RootSliceOverlap i j k l γ × ℝ)} (hS : MeasurableSet S) :
    A.overlapMeasure γ l μ S =
      μ (rootOverlapParam hij γ '' (S ∩ A.overlapDomain γ l)) := by
  let U := {s : RootSlice i j k | (γ * s.val).1 l i ≠ 0}
  have he := baseSubtypeMap_embedding (β := ℝ) U (rootSliceOverlap_isOpen γ).measurableSet
  rw [overlapMeasure,he.comap_apply,A.coordinateMeasure_apply μ (he.measurableSet_image.mpr hS)]
  congr 1
  ext x
  constructor
  · rintro ⟨z,⟨⟨w,hw,rfl⟩,hd⟩,rfl⟩
    exact ⟨w,⟨hw,hd⟩,rfl⟩
  · rintro ⟨w,⟨hw,hd⟩,rfl⟩
    exact ⟨baseSubtypeMap U w,⟨⟨w,hw,rfl⟩,hd⟩,rfl⟩

lemma overlapMeasure_conditional (A : RootBox hij k) (γ : G n) (l : Fin n)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(A.overlapMeasure γ l μ).fst,
      (A.overlapMeasure γ l μ).condKernel s = A.conditionalKernel μ s.val :=
  conditional_comap_baseSubtype (A.coordinateMeasure μ) _ (rootSliceOverlap_isOpen γ).measurableSet

 

theorem overlapMeasure_transition (A : RootBox hij k) (B : RootBox hij l)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) :
    ((A.overlapMeasure γ l μ).restrict
      ((rootTransitionCoordinates hij γ) ⁻¹' B.overlapDomain γ⁻¹ k)).map
        (rootTransitionCoordinates hij γ) =
      (B.overlapMeasure γ⁻¹ k μ).restrict
        (rootTransitionCoordinates hij γ '' A.overlapDomain γ l) := by
  let E := rootTransitionCoordinates (k := k) (l := l) hij γ
  ext S hS
  rw [Measure.map_apply E.measurable hS,Measure.restrict_apply (E.measurable hS),
    A.overlapMeasure_apply γ l μ ((E.measurable hS).inter
      (E.measurable (B.overlapDomain_open γ⁻¹ k).measurableSet)),
    Measure.restrict_apply hS,B.overlapMeasure_apply γ⁻¹ k μ
      (hS.inter (E.measurableEmbedding.measurableSet_image.mpr
        (A.overlapDomain_open γ l).measurableSet))]
  congr 1
  ext x
  constructor
  · rintro ⟨z,⟨⟨hzS,hzB⟩,hzA⟩,rfl⟩
    exact ⟨E z,⟨⟨hzS,⟨z,hzA,rfl⟩⟩,hzB⟩,rootTransitionCoordinates_param hij γ hγ z⟩
  · rintro ⟨w,⟨⟨hwS,z,hzA,rfl⟩,hzB⟩,rfl⟩
    exact ⟨z,⟨⟨hwS,hzB⟩,hzA⟩,(rootTransitionCoordinates_param hij γ hγ z).symm⟩

end RootBox
end PrimeDegreePackets


namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k l : Fin n} {hij : i ≠ j}

theorem overlap_conditional_projective (A : RootBox hij k) (B : RootBox hij l)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) [IsFiniteMeasure μ] :
    let E := rootTransitionCoordinates (k := k) (l := l) hij γ
    let T := E ⁻¹' B.overlapDomain γ⁻¹ k
    let W := E '' A.overlapDomain γ l
    ∀ᵐ s ∂((A.overlapMeasure γ l μ).restrict T).fst,
      A.conditionalKernel μ s.val (Prod.mk s ⁻¹' T) ≠ 0 ∧
      B.conditionalKernel μ (rootTransitionSlice hij γ s).val
        (Prod.mk (rootTransitionSlice hij γ s) ⁻¹' W) ≠ 0 ∧
      ((anchorNormalize (A.conditionalKernel μ s.val) (Prod.mk s ⁻¹' T)).restrict
        (Prod.mk s ⁻¹' T)).map (Homeomorph.addRight (rootTransitionTime γ s)) =
      (anchorNormalize (B.conditionalKernel μ (rootTransitionSlice hij γ s).val)
        (Prod.mk (rootTransitionSlice hij γ s) ⁻¹' W)).restrict
        (Prod.mk (rootTransitionSlice hij γ s) ⁻¹' W) := by
  intro E T W
  let e := (rootSliceTransition (k := k) (l := l) hij γ).toMeasurableEquiv
  let F : RootSliceOverlap i j k l γ × ℝ → ℝ := fun z => z.2 + rootTransitionTime γ z.1
  have hF : Measurable F := measurable_snd.add
    ((continuous_rootTransitionTime γ).measurable.comp measurable_fst)
  have H := conditional_overlap_normalized (A.overlapMeasure γ l μ) (B.overlapMeasure γ⁻¹ k μ)
    T (E.measurable (B.overlapDomain_open γ⁻¹ k).measurableSet)
    W (E.measurableEmbedding.measurableSet_image.mpr (A.overlapDomain_open γ l).measurableSet)
    e F hF (A.overlapMeasure_transition B γ hγ μ)
  have HA : ∀ᵐ s ∂((A.overlapMeasure γ l μ).restrict T).fst,
      (A.overlapMeasure γ l μ).condKernel s = A.conditionalKernel μ s.val :=
    (Measure.absolutelyContinuous_of_le (Measure.fst_mono Measure.restrict_le_self)).ae_le
      (A.overlapMeasure_conditional γ l μ)
  have HB : ∀ᵐ t ∂((B.overlapMeasure γ⁻¹ k μ).restrict W).fst,
      (B.overlapMeasure γ⁻¹ k μ).condKernel t = B.conditionalKernel μ t.val :=
    (Measure.absolutelyContinuous_of_le (Measure.fst_mono Measure.restrict_le_self)).ae_le
      (B.overlapMeasure_conditional γ⁻¹ k μ)
  have hm := congrArg Measure.fst (A.overlapMeasure_transition B γ hγ μ)
  change (((A.overlapMeasure γ l μ).restrict T).map (fun z => (e z.1,F z))).fst = _ at hm
  rw [fst_map_fibers _ e F hF] at hm
  rw [←hm] at HB
  have HB' := ae_of_ae_map e.measurable.aemeasurable HB
  filter_upwards [H,HA,HB'] with s hs ha hb
  rw [ha,hb] at hs
  exact hs

end PrimeDegreePackets.RootBox


namespace PrimeDegreePackets

namespace RootBox
variable {n : ℕ} {i j k l : Fin n} {hij : i ≠ j}

abbrev transitionOverlapMeasure (A : RootBox hij k) (B : RootBox hij l)
    (γ : G n) (μ : Measure (X n)) : Measure (RootSliceOverlap i j k l γ × ℝ) :=
  (A.overlapMeasure γ l μ).restrict
    ((rootTransitionCoordinates hij γ) ⁻¹' B.overlapDomain γ⁻¹ k)

lemma transitionOverlapMeasure_apply (A : RootBox hij k) (B : RootBox hij l)
    (γ : G n) (μ : Measure (X n)) {S : Set (RootSliceOverlap i j k l γ × ℝ)}
    (hS : MeasurableSet S) :
    A.transitionOverlapMeasure B γ μ S = μ (rootOverlapParam hij γ ''
      ((S ∩ (rootTransitionCoordinates hij γ) ⁻¹' B.overlapDomain γ⁻¹ k) ∩ A.overlapDomain γ l)) := by
  rw [transitionOverlapMeasure,Measure.restrict_apply hS,A.overlapMeasure_apply γ l μ
    (hS.inter ((rootTransitionCoordinates hij γ).measurable (B.overlapDomain_open γ⁻¹ k).measurableSet))]

 

lemma transitionOverlapMeasure_restrict_le (A D : RootBox hij k) (B F : RootBox hij l)
    (hAD : A.time ⊆ D.time) (hBF : B.time ⊆ F.time)
    (γ : G n) (μ : Measure (X n)) :
    (A.transitionOverlapMeasure B γ μ).restrict (Prod.fst ⁻¹'
      {s | s.val ∈ D.transverse ∧ (rootTransitionSlice hij γ s).val ∈ F.transverse}) ≤
      D.transitionOverlapMeasure F γ μ := by
  let U := {s : RootSliceOverlap i j k l γ |
    s.val ∈ D.transverse ∧ (rootTransitionSlice hij γ s).val ∈ F.transverse}
  have hU : MeasurableSet U :=
    (measurable_subtype_coe D.transverse_open.measurableSet).inter
      ((continuous_rootTransitionSlice hij γ).measurable
        (measurable_subtype_coe F.transverse_open.measurableSet))
  apply Measure.le_iff.mpr
  intro S hS
  have hSU : MeasurableSet (S ∩ Prod.fst ⁻¹' U) := hS.inter (measurable_fst hU)
  rw [Measure.restrict_apply hS,transitionOverlapMeasure_apply _ _ _ _ hSU,
    transitionOverlapMeasure_apply _ _ _ _ hS]
  apply measure_mono
  apply Set.image_mono
  rintro z ⟨⟨⟨hzS,hzD,hzF⟩,hzB⟩,hzA⟩
  exact ⟨⟨hzS,⟨hzF,hBF hzB.2⟩⟩,⟨hzD,hAD hzA.2⟩⟩

lemma transition_base_ae_of_ae (A D : RootBox hij k) (B F : RootBox hij l)
    (hAD : A.time ⊆ D.time) (hBF : B.time ⊆ F.time)
    (γ : G n) (μ : Measure (X n)) {P : RootSliceOverlap i j k l γ → Prop}
    (hP : ∀ᵐ s ∂(D.transitionOverlapMeasure F γ μ).fst, P s) :
    ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst,
      s.val ∈ D.transverse → (rootTransitionSlice hij γ s).val ∈ F.transverse → P s := by
  let U := {s : RootSliceOverlap i j k l γ |
    s.val ∈ D.transverse ∧ (rootTransitionSlice hij γ s).val ∈ F.transverse}
  have hU : MeasurableSet U :=
    (measurable_subtype_coe D.transverse_open.measurableSet).inter
      ((continuous_rootTransitionSlice hij γ).measurable
        (measurable_subtype_coe F.transverse_open.measurableSet))
  have H := (Measure.absolutelyContinuous_of_le
    (Measure.fst_mono (A.transitionOverlapMeasure_restrict_le D B F hAD hBF γ μ))).ae_le hP
  rw [fst_restrict_base _ hU] at H
  filter_upwards [(ae_restrict_iff' hU).mp H] with s hs
  exact fun hD hF => hs ⟨hD,hF⟩

lemma transition_base_ae_source (A : RootBox hij k) (B : RootBox hij l)
    (γ : G n) (μ : Measure (X n)) [IsFiniteMeasure μ]
    {P : RootSlice i j k → Prop} (hP : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, P s) :
    ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst, P s.val := by
  let U := {s : RootSlice i j k | (γ*s.val).1 l i ≠ 0}
  have H := (Measure.absolutelyContinuous_of_le (Measure.restrict_le_self (s := U))).ae_le hP
  rw [←fst_map_comap_baseSubtype (A.coordinateMeasure μ) U
    (rootSliceOverlap_isOpen γ).measurableSet] at H
  exact (Measure.absolutelyContinuous_of_le (Measure.fst_mono Measure.restrict_le_self)).ae_le
    (ae_of_ae_map measurable_subtype_coe.aemeasurable H)

lemma transition_base_ae_target (A : RootBox hij k) (B : RootBox hij l)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) [IsFiniteMeasure μ]
    {P : RootSlice i j l → Prop} (hP : ∀ᵐ s ∂(B.coordinateMeasure μ).fst, P s) :
    ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst, P (rootTransitionSlice hij γ s).val := by
  let U := {s : RootSlice i j l | (γ⁻¹*s.val).1 k i ≠ 0}
  have H := (Measure.absolutelyContinuous_of_le (Measure.restrict_le_self (s := U))).ae_le hP
  rw [←fst_map_comap_baseSubtype (B.coordinateMeasure μ) U
    (rootSliceOverlap_isOpen γ⁻¹).measurableSet] at H
  have H' := ae_of_ae_map measurable_subtype_coe.aemeasurable H
  have H'' := (Measure.absolutelyContinuous_of_le (Measure.fst_mono
    (Measure.restrict_le_self (s := rootTransitionCoordinates hij γ '' A.overlapDomain γ l)))).ae_le H'
  change ∀ᵐ s ∂((B.overlapMeasure γ⁻¹ k μ).restrict
    (rootTransitionCoordinates hij γ '' A.overlapDomain γ l)).fst, P s.val at H''
  rw [←A.overlapMeasure_transition B γ hγ μ] at H''
  have hm := fst_map_fibers (A.transitionOverlapMeasure B γ μ)
    (rootSliceTransition hij γ).toMeasurableEquiv
    (fun z => z.2 + rootTransitionTime γ z.1)
    (measurable_snd.add ((continuous_rootTransitionTime γ).measurable.comp measurable_fst))
  change ((A.transitionOverlapMeasure B γ μ).map (rootTransitionCoordinates hij γ)).fst = _ at hm
  rw [hm] at H''
  exact ae_of_ae_map (rootSliceTransition hij γ).measurable.aemeasurable H''

end RootBox
end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafTransitions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
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
namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k l : Fin n} {hij : i ≠ j}

lemma transition_source_fiber (B : RootBox hij l) (γ : G n)
    (s : RootSliceOverlap i j k l γ)
    (hs : (rootTransitionSlice hij γ s).val ∈ B.transverse) :
    Prod.mk s ⁻¹' ((rootTransitionCoordinates hij γ) ⁻¹' B.overlapDomain γ⁻¹ k) =
      (Homeomorph.addRight (rootTransitionTime γ s)) ⁻¹' B.time := by
  ext t
  change (_ ∧ _) ↔ _
  exact and_iff_right hs

lemma transition_target_fiber (A : RootBox hij k) (γ : G n)
    (s : RootSliceOverlap i j k l γ) (hs : s.val ∈ A.transverse) :
    Prod.mk (rootTransitionSlice hij γ s) ⁻¹'
      ((rootTransitionCoordinates hij γ) '' A.overlapDomain γ l) =
      (Homeomorph.addRight (rootTransitionTime γ s)) '' A.time := by
  ext t
  constructor
  · rintro ⟨z,hz,he⟩
    have hbase : (rootSliceTransition hij γ) z.1 = (rootSliceTransition hij γ) s :=
      congrArg Prod.fst he
    have hzs : z.1 = s := (rootSliceTransition hij γ).injective hbase
    refine ⟨z.2,hz.2,?_⟩
    have ht := congrArg Prod.snd he
    change z.2 + rootTransitionTime γ z.1 = t at ht
    change z.2 + rootTransitionTime γ s = t
    simpa only [hzs] using ht
  · rintro ⟨v,hv,rfl⟩
    exact ⟨(s,v),⟨hs,hv⟩,rfl⟩

 

theorem overlap_conditional_projective_explicit (A : RootBox hij k) (B : RootBox hij l)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst,
      let f := Homeomorph.addRight (rootTransitionTime γ s)
      A.conditionalKernel μ s.val (f ⁻¹' B.time) ≠ 0 ∧
      B.conditionalKernel μ (rootTransitionSlice hij γ s).val (f '' A.time) ≠ 0 ∧
      ((anchorNormalize (A.conditionalKernel μ s.val) (f ⁻¹' B.time)).restrict (f ⁻¹' B.time)).map f =
      (anchorNormalize (B.conditionalKernel μ (rootTransitionSlice hij γ s).val) (f '' A.time)).restrict
        (f '' A.time) := by
  have HA := A.transition_base_ae_source B γ μ (A.coordinateMeasure_fst_ae_transverse μ)
  have HB := A.transition_base_ae_target B γ hγ μ (B.coordinateMeasure_fst_ae_transverse μ)
  filter_upwards [A.overlap_conditional_projective B γ hγ μ,HA,HB] with s hs ha hb
  simpa only [B.transition_source_fiber γ s hb,A.transition_target_fiber γ s ha] using hs

end PrimeDegreePackets.RootBox


namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k l : Fin n} {hij : i ≠ j}

lemma ae_leafMeasure_restrict_conditional (A D : RootBox hij k)
    (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) (hAD : A.time ⊆ D.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ D.transverse →
      D.conditionalKernel μ s A.time ≠ 0 ∧
      (A.leafMeasure R μ s).restrict D.time =
        (D.conditionalKernel μ s A.time)⁻¹ • D.conditionalKernel μ s := by
  have H := base_ae_of_ae A D hAD μ (D.conditionalKernel_ae_time μ)
  filter_upwards [A.ae_leafMeasure_restrict R hAR μ hfree D hAD,H] with s hs ht
  intro hsD
  refine ⟨(hs hsD).1,?_⟩
  rw [(hs hsD).2,anchorNormalize,Measure.restrict_smul,
    Measure.restrict_eq_self_of_ae_mem (ht hsD)]

 

theorem ae_leafTransition_restrict (A D : RootBox hij k) (B F : RootBox hij l)
    (R S : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (hAD : A.time ⊆ D.time) (hBF : B.time ⊆ F.time)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst,
      s.val ∈ D.transverse → (rootTransitionSlice hij γ s).val ∈ F.transverse →
      let f := Homeomorph.addRight (rootTransitionTime γ s)
      let J := A.time ∩ f ⁻¹' B.time
      ((anchorNormalize (A.leafMeasure R μ s.val) J).restrict
        (f ⁻¹' F.time ∩ D.time)).map f =
      (anchorNormalize (B.leafMeasure S μ (rootTransitionSlice hij γ s).val) (f '' J)).restrict
        (f '' D.time ∩ F.time) := by
  have HA := A.transition_base_ae_source B γ μ
    (A.ae_leafMeasure_restrict_conditional D R hAR hAD μ hfree)
  have HB := A.transition_base_ae_target B γ hγ μ
    (B.ae_leafMeasure_restrict_conditional F S hBS hBF μ hfree)
  have HD := A.transition_base_ae_of_ae D B F hAD hBF γ μ
    (D.overlap_conditional_projective_explicit F γ hγ μ)
  filter_upwards [HA,HB,HD] with s ha hb hd
  intro hsD hsF f J
  have hJ : MeasurableSet J := A.time_open.measurableSet.inter (f.measurable B.time_open.measurableSet)
  have hJD : J ⊆ D.time := inter_subset_left.trans hAD
  have hJV : J ⊆ f ⁻¹' F.time := fun t ht => hBF ht.2
  have hJE : f '' J ⊆ F.time := by
    rintro _ ⟨t,ht,rfl⟩
    exact hBF ht.2
  have hJW : f '' J ⊆ f '' D.time := image_mono hJD
  have hDA := ha hsD
  have hFB := hb hsF
  have hDF := hd hsD hsF
  exact projective_extensions_overlap _ _ _ _ f.toMeasurableEquiv
    D.time_open.measurableSet F.time_open.measurableSet hJ hJD hJV hJE hJW
    _ _ (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (ENNReal.inv_ne_top.mpr hDA.1)
    (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (ENNReal.inv_ne_top.mpr hFB.1)
    hDA.2 hFB.2 hDF.1 (measure_ne_top _ _) hDF.2.1 (measure_ne_top _ _) hDF.2.2

end PrimeDegreePackets.RootBox


namespace PrimeDegreePackets

namespace RootBox
variable {n : ℕ} {i j k l : Fin n} {hij : i ≠ j}

 

theorem ae_leafTransition (A : RootBox hij k) (B : RootBox hij l)
    (R S : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst,
      let f := Homeomorph.addRight (rootTransitionTime γ s)
      let J := A.time ∩ f ⁻¹' B.time
      (anchorNormalize (A.leafMeasure R μ s.val) J).map f =
        anchorNormalize (B.leafMeasure S μ (rootTransitionSlice hij γ s).val) (f '' J) := by
  let C := rootLongBoxFamily hij k R
  let D := rootLongBoxFamily hij l S
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  let (m : ℕ) : Countable (D m) := (rootLongBoxFamily_countable hij l S m).to_subtype
  have hC (m : ℕ) (K : C m) : K.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m K.val K.prop
  have hD (m : ℕ) (L : D m) : L.val.time = rootLeafWindow S m :=
    rootLongBoxFamily_time hij l S m L.val L.prop
  have hAC (m : ℕ) (K : C m) : A.time ⊆ K.val.time := by
    rw [hC m K]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have hBD (m : ℕ) (L : D m) : B.time ⊆ L.val.time := by
    rw [hD m L]
    exact hBS.trans (rootLeafWindow_mono S (Nat.zero_le m))
  have H : ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst,
      ∀ (m : ℕ) (K : C m) (L : D m), s.val ∈ K.val.transverse →
        (rootTransitionSlice hij γ s).val ∈ L.val.transverse →
      let f := Homeomorph.addRight (rootTransitionTime γ s)
      let J := A.time ∩ f ⁻¹' B.time
      ((anchorNormalize (A.leafMeasure R μ s.val) J).restrict
        (f ⁻¹' L.val.time ∩ K.val.time)).map f =
      (anchorNormalize (B.leafMeasure S μ (rootTransitionSlice hij γ s).val) (f '' J)).restrict
        (f '' K.val.time ∩ L.val.time) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro K
    apply ae_all_iff.mpr
    intro L
    exact A.ae_leafTransition_restrict K.val B L.val R S hAR hBS (hAC m K) (hBD m L) γ hγ μ hfree
  have HA := A.transition_base_ae_source B γ μ (A.ae_injective_root_slice_of_ae_free μ hfree)
  have HB := A.transition_base_ae_target B γ hγ μ (B.ae_injective_root_slice_of_ae_free μ hfree)
  filter_upwards [H,HA,HB] with s hs ha hb
  intro f J
  let W := fun m => f '' rootLeafWindow R m ∩ rootLeafWindow S m
  have hW : Monotone W := fun a b hab =>
    inter_subset_inter (image_mono (rootLeafWindow_mono R hab)) (rootLeafWindow_mono S hab)
  apply measure_eq_of_restrictionChain W hW (translated_window_chain_cover R S (rootTransitionTime γ s))
  intro m
  obtain ⟨K,hKC,hsK⟩ := rootLongBoxFamily_covers hij k R m s.val ha
  obtain ⟨L,hLD,hsL⟩ := rootLongBoxFamily_covers hij l S m (rootTransitionSlice hij γ s).val hb
  let K' : C m := ⟨K,hKC⟩
  let L' : D m := ⟨L,hLD⟩
  have he := hs m K' L' hsK hsL
  rw [hC m K',hD m L'] at he
  rw [f.measurableEmbedding.restrict_map]
  have hpre : f ⁻¹' W m = f ⁻¹' rootLeafWindow S m ∩ rootLeafWindow R m := by
    rw [show W m = f '' rootLeafWindow R m ∩ rootLeafWindow S m from rfl,
      preimage_inter,f.preimage_image,inter_comm]
  rw [hpre]
  exact he

 

theorem ae_leafTransition_anchor_mass (A : RootBox hij k) (B : RootBox hij l)
    (R S : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst,
      let f := Homeomorph.addRight (rootTransitionTime γ s)
      let J := A.time ∩ f ⁻¹' B.time
      A.leafMeasure R μ s.val J ≠ 0 ∧ A.leafMeasure R μ s.val J ≠ ∞ ∧
      B.leafMeasure S μ (rootTransitionSlice hij γ s).val (f '' J) ≠ 0 ∧
      B.leafMeasure S μ (rootTransitionSlice hij γ s).val (f '' J) ≠ ∞ := by
  have HA := A.transition_base_ae_source B γ μ (A.ae_leafMeasure_spec R hAR μ hfree)
  have HB := A.transition_base_ae_target B γ hγ μ (B.ae_leafMeasure_spec S hBS μ hfree)
  filter_upwards [HA,HB,A.overlap_conditional_projective_explicit B γ hγ μ] with s ha hb he
  intro f J
  have hA : A.leafMeasure R μ s.val J = A.conditionalKernel μ s.val (f ⁻¹' B.time) := by
    have H := congrArg (fun ν : Measure ℝ => ν (f ⁻¹' B.time)) ha.2.2.1
    simpa only [Measure.restrict_apply (f.measurable B.time_open.measurableSet),inter_comm] using H
  have hB : B.leafMeasure S μ (rootTransitionSlice hij γ s).val (f '' J) =
      B.conditionalKernel μ (rootTransitionSlice hij γ s).val (f '' A.time) := by
    have H := congrArg (fun ν : Measure ℝ => ν (f '' A.time)) hb.2.2.1
    have hset : f '' J = f '' A.time ∩ B.time := by
      rw [show J = A.time ∩ f ⁻¹' B.time from rfl,image_inter_preimage]
    rw [hset]
    simpa only [Measure.restrict_apply (f.measurableEmbedding.measurableSet_image.mpr
      A.time_open.measurableSet)] using H
  rw [hA,hB]
  exact ⟨he.1,measure_ne_top _ _,he.2.1,measure_ne_top _ _⟩

 

theorem ae_basedLeaf_transition (A : RootBox hij k) (B : RootBox hij l)
    (R S : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst, ∀ t : ℝ,
      A.basedLeaf R μ (s.val,t) = B.basedLeaf S μ
        ((rootTransitionSlice hij γ s).val,t + rootTransitionTime γ s) := by
  filter_upwards [A.ae_leafTransition B R S hAR hBS γ hγ μ hfree,
    A.ae_leafTransition_anchor_mass B R S hAR hBS γ hγ μ hfree] with s hs hm
  intro t
  have H := congrArg (fun ν : Measure ℝ => basedRealMeasure ν (t + rootTransitionTime γ s)) hs
  rw [basedRealMeasure_translate] at H
  unfold anchorNormalize at H
  rw [basedRealMeasure_smul _ _ (ENNReal.inv_ne_zero.mpr hm.2.1) (ENNReal.inv_ne_top.mpr hm.1),
    basedRealMeasure_smul _ _ (ENNReal.inv_ne_zero.mpr hm.2.2.2)
      (ENNReal.inv_ne_top.mpr hm.2.2.1)] at H
  exact H

end RootBox
end PrimeDegreePackets

open scoped Matrix Topology Classical ENNReal
namespace PrimeDegreePackets
variable {n : ℕ} {i j k l : Fin n} (hij : i ≠ j)

lemma rootGroupParametrization_injective :
    Function.Injective (fun z : RootSlice i j k × ℝ => ((rootPivotHomeomorph hij).symm z).val) := by
  intro z w h
  exact (rootPivotHomeomorph hij).symm.injective (Subtype.ext h)

 

theorem exists_rootTransition_of_quotient_eq
    (z : RootSlice i j k × ℝ) (w : RootSlice i j l × ℝ)
    (he : rootQuotientParametrization hij z = rootQuotientParametrization hij w) :
    ∃ γ : integralGroup n, ∃ h : (γ.val * z.1.val).1 l i ≠ 0,
      baseSubtypeMap {s : RootSlice i j l | (γ.val⁻¹ * s.val).1 k i ≠ 0}
        (rootTransitionCoordinates hij γ.val (⟨z.1,h⟩,z.2)) = w := by
  let g := ((rootPivotHomeomorph hij).symm z).val
  let h := ((rootPivotHomeomorph hij).symm w).val
  let γ := h*g⁻¹
  have hγ : γ ∈ integralGroup n := by
    exact (QuotientGroup.rightRel_apply.mp (Quotient.exact he))
  have heq : γ*g = h := by simp [γ,mul_assoc]
  have hp : (γ*z.1.val).1 l i ≠ 0 := by
    have hc := congrArg (fun q : G n => q.1 l i) heq
    change (γ*(z.1.val*Matrix.SpecialLinearGroup.transvection hij z.2)).1 l i = h.1 l i at hc
    rw [←mul_assoc,root_mul_entry,ite_eq_right hij,add_zero] at hc
    rw [hc]
    exact ((rootPivotHomeomorph hij).symm w).prop
  refine ⟨⟨γ,hγ⟩,hp,?_⟩
  apply rootGroupParametrization_injective hij
  exact (rootTransition_reconstruct hij γ ⟨z.1,hp⟩ z.2).trans heq

end PrimeDegreePackets


namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k l : Fin n} {hij : i ≠ j}

lemma map_transitionOverlapMeasure (A : RootBox hij k) (B : RootBox hij l)
    (γ : G n) (μ : Measure (X n)) :
    (A.transitionOverlapMeasure B γ μ).map
      (baseSubtypeMap {s : RootSlice i j k | (γ * s.val).1 l i ≠ 0}) =
    (A.coordinateMeasure μ).restrict
      (baseSubtypeMap {s : RootSlice i j k | (γ * s.val).1 l i ≠ 0} ''
        ((rootTransitionCoordinates hij γ) ⁻¹' B.overlapDomain γ⁻¹ k)) := by
  let U := {s : RootSlice i j k | (γ * s.val).1 l i ≠ 0}
  let T := (rootTransitionCoordinates hij γ) ⁻¹' B.overlapDomain γ⁻¹ k
  have he := baseSubtypeMap_embedding (β := ℝ) U (rootSliceOverlap_isOpen γ).measurableSet
  change ((A.coordinateMeasure μ).comap (baseSubtypeMap U) |>.restrict T).map (baseSubtypeMap U) = _
  rw [he.restrict_comap,he.map_comap,baseSubtypeMap_range]
  change ((A.coordinateMeasure μ).restrict (baseSubtypeMap U '' T)).restrict (U ×ˢ univ) =
    (A.coordinateMeasure μ).restrict (baseSubtypeMap U '' T)
  rw [Measure.restrict_restrict (MeasurableSet.prod (rootSliceOverlap_isOpen γ).measurableSet MeasurableSet.univ)]
  congr 1
  apply inter_eq_right.mpr
  rw [←baseSubtypeMap_range (β := ℝ) U]
  exact image_subset_range _ _

lemma ae_basedLeaf_lift_transition (A : RootBox hij k) (B : RootBox hij l)
    (R S : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ, ∀ hp : (γ*z.1.val).1 l i ≠ 0,
      (rootTransitionCoordinates hij γ (⟨z.1,hp⟩,z.2)) ∈ B.overlapDomain γ⁻¹ k →
      A.basedLeaf R μ z = B.basedLeaf S μ
        (baseSubtypeMap {s : RootSlice i j l | (γ⁻¹*s.val).1 k i ≠ 0}
          (rootTransitionCoordinates hij γ (⟨z.1,hp⟩,z.2))) := by
  let U := {s : RootSlice i j k | (γ*s.val).1 l i ≠ 0}
  let T := (rootTransitionCoordinates hij γ) ⁻¹' B.overlapDomain γ⁻¹ k
  let P := fun z : RootSlice i j k × ℝ => ∀ hp : (γ*z.1.val).1 l i ≠ 0,
    (rootTransitionCoordinates hij γ (⟨z.1,hp⟩,z.2)) ∈ B.overlapDomain γ⁻¹ k →
      A.basedLeaf R μ z = B.basedLeaf S μ
        (baseSubtypeMap {s : RootSlice i j l | (γ⁻¹*s.val).1 k i ≠ 0}
          (rootTransitionCoordinates hij γ (⟨z.1,hp⟩,z.2)))
  have H : ∀ᵐ z ∂A.transitionOverlapMeasure B γ μ, P (baseSubtypeMap U z) := by
    have H₀ := ae_of_ae_map measurable_fst.aemeasurable
      (A.ae_basedLeaf_transition B R S hAR hBS γ hγ μ hfree)
    filter_upwards [H₀] with z hz
    intro hp _
    exact hz z.2
  have he := baseSubtypeMap_embedding (β := ℝ) U (rootSliceOverlap_isOpen γ).measurableSet
  have H' := he.ae_map_iff.mpr H
  rw [map_transitionOverlapMeasure] at H'
  have hT : MeasurableSet T :=
    (rootTransitionCoordinates hij γ).measurable (B.overlapDomain_open γ⁻¹ k).measurableSet
  have H'' := (ae_restrict_iff' (he.measurableSet_image.mpr hT)).mp H'
  filter_upwards [H''] with z hz
  intro hp ht
  exact hz ⟨(⟨z.1,hp⟩,z.2),ht,rfl⟩ hp ht

 

theorem ae_basedLeaf_chart_compatibility (A : RootBox hij k) (B : RootBox hij l)
    (R S : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ, ∀ w ∈ B.domain,
      rootQuotientParametrization hij z = rootQuotientParametrization hij w →
      A.basedLeaf R μ z = B.basedLeaf S μ w := by
  let : Countable (Matrix.SpecialLinearGroup (Fin n) ℤ) := by
    unfold Matrix.SpecialLinearGroup Matrix
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : Countable (integralGroup n) :=
    (Set.countable_range (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) :
      Matrix.SpecialLinearGroup (Fin n) ℤ → G n)).to_subtype
  have H := ae_all_iff.mpr (fun γ : integralGroup n =>
    A.ae_basedLeaf_lift_transition B R S hAR hBS γ.val γ.prop μ hfree)
  filter_upwards [H] with z hz
  intro w hw he
  obtain ⟨γ,hp,heq⟩ := exists_rootTransition_of_quotient_eq hij z w he
  have ht : rootTransitionCoordinates hij γ.val (⟨z.1,hp⟩,z.2) ∈ B.overlapDomain γ.val⁻¹ k := by
    change baseSubtypeMap _ _ ∈ B.domain
    rwa [heq]
  exact (hz γ hp ht).trans (congrArg (B.basedLeaf S μ) heq)

end PrimeDegreePackets.RootBox


namespace PrimeDegreePackets
variable {n : ℕ} {i j : Fin n} (hij : i ≠ j)

namespace RootBox
variable {hij} {k : Fin n}



lemma param_coordinates (A : RootBox hij k) (x : A.range) :
    A.param (A.coordinates x) = x.val := by
  exact congrArg Subtype.val (A.embedding.toIsEmbedding.toHomeomorph.apply_symm_apply x)

lemma aemeasurable_of_coordinate (A : RootBox hij k) (μ : Measure (X n))
    {β : Type*} [MeasurableSpace β] {f : X n → β}
    (hf : AEMeasurable (f ∘ rootQuotientParametrization hij) (A.coordinateMeasure μ)) :
    AEMeasurable f (μ.restrict A.range) := by
  have he : (μ.comap A.param).map A.param = μ.restrict A.range :=
    A.embedding.measurableEmbedding.map_comap μ
  rw [←he]
  apply A.embedding.measurableEmbedding.aemeasurable_map_iff.mpr
  exact hf.comp_measurable measurable_subtype_coe

end RootBox

lemma boundedRootAtlas_countable : (boundedRootAtlas hij).Countable :=
  (exists_countable_boundedRootBox_cover hij).choose_spec.1

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntrinsicLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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
variable {n : ℕ} {i j : Fin n} (hij : i ≠ j)



namespace RootBox
variable {hij} {k : Fin n}

 

theorem ae_intrinsicRootLeaf_coordinates (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) = A.basedLeaf R μ z := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H := ae_all_iff.mpr (fun B : boundedRootAtlas hij =>
    A.ae_basedLeaf_chart_compatibility B.val.box R B.val.radius hAR B.val.time_bound μ hfree)
  filter_upwards [H] with z hz
  let x := rootQuotientParametrization hij z
  let B := selectedRootBox hij x
  let w := B.val.box.coordinates ⟨x,selectedRootBox_mem hij x⟩
  exact (hz B w.val w.prop (B.val.box.param_coordinates ⟨x,selectedRootBox_mem hij x⟩).symm).symm

lemma aemeasurable_intrinsicRootLeaf_restrict (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    AEMeasurable (intrinsicRootLeaf hij μ) (μ.restrict A.range) := by
  apply A.aemeasurable_of_coordinate μ
  exact (A.aemeasurable_basedLeaf R hAR μ hfree).congr
    ((A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree).mono (fun z hz => hz.symm))

end RootBox

lemma boundedRootAtlas_iUnion : (⋃ B : boundedRootAtlas hij, B.val.box.range) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨B,hB⟩ := boundedRootAtlas_covers hij x
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem aemeasurable_intrinsicRootLeaf (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    AEMeasurable (intrinsicRootLeaf hij μ) μ := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H := AEMeasurable.iUnion (μ := μ) (fun B : boundedRootAtlas hij =>
    B.val.box.aemeasurable_intrinsicRootLeaf_restrict B.val.radius B.val.time_bound μ hfree)
  simpa only [boundedRootAtlas_iUnion,Measure.restrict_univ] using H



def intrinsicRootKernel (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    Kernel (X n) ℝ := locallyFiniteRealVersion
      ⟨(aemeasurable_intrinsicRootLeaf hij μ hfree).mk (intrinsicRootLeaf hij μ),
        (aemeasurable_intrinsicRootLeaf hij μ hfree).measurable_mk⟩

instance intrinsicRootKernel_sFinite (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    IsSFiniteKernel (intrinsicRootKernel hij μ hfree) := locallyFiniteRealVersion_sFinite _

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafLusin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact sets with continuous root-leaf data

The Lusin step in EKL (2006), Section 4.3, is applied to a countable
family of compactly supported tests determining locally finite real
measures. A finer Polish topology and inner regularity provide a compact
set in the original topology, outside any specified null set.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology Classical ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

def intrinsicLeafData {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (x : X n) : (ℕ × ℕ) → ℝ := fun q =>
  ∫ t, leafTest q.1 q.2 t ∂intrinsicRootKernel hij μ hfree x

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_LeafFlowCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

def rootPairCovarianceKernel
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    Kernel (X n × ℝ) ℝ :=
  normalizedRescaledRealKernel (Kernel.prodMkRight ℝ (intrinsicRootKernel hij μ hfree))
    (fun p => Real.exp (-2 * p.2)) (by fun_prop)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RegularLusinSets
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Regular Lusin sets and regular maximal-inequality base points

Removing the single regularity null set from the base-point good set
does not change its measure bound. The compact Lusin set can avoid that
null set and any additional prescribed null set at the same time.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def RootLeafRegular {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0)
    (x : X n) : Prop :=
  intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x ∧
    IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) ∧
    (∀ r : ℝ, 0 < r → 0 < intrinsicRootLeaf hij μ x (Metric.ball 0 r)) ∧
    ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
      intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
        basedRealMeasure (intrinsicRootLeaf hij μ x) t

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPairTimeSelection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual diagonal recurrence with simultaneous leaf covariance

The correct two-coordinate shearing flow has a large measurable set on
which both recurrence estimates hold on every long interval. Removing
one null set also gives leaf covariance at almost every time. The common
time can therefore satisfy all six recurrence conditions and all six
covariance identities used in the two-scale argument.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def RootPairLeafCovariance {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (x : X n) (t : ℝ) : Prop :=
  intrinsicRootKernel hij μ hfree (rightAction x (rootPairFlow i j (-t))) =
    rootPairCovarianceKernel hij μ hfree (x, t)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingSelectionData
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual sets used for the low-entropy shearing argument

The constants are fixed for this application. The two maximal estimates,
Lusin continuity, small central leaf mass, arithmetic freeness and leaf
regularity are all supplied by proved results. In particular the source
set has positive measure, so the neutral return theorem applies to it.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

structure RootPairSelectionData (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0)
    (N : Set (X (d + 1))) where
  K : Set (X (d + 1))
  G : Set (X (d + 1))
  H : Set (X (d + 1))
  Z : Set (X (d + 1))
  ρ : ℝ
  rho_pos : 0 < ρ
  rho_small : ρ < 1 / 2
  compact : IsCompact K
  outside : K ⊆ Nᶜ
  continuous : ContinuousOn (intrinsicLeafData hij μ hfree) K
  compact_regular : ∀ x ∈ K, RootLeafRegular hij μ hfree x
  coordinates : ∀ x ∈ K, ∀ v ∈ pointLattice x, v ≠ 0 → ∀ k, v k ≠ 0
  good_regular : ∀ x ∈ G, RootLeafRegular hij μ hfree x
  good_returns : ∀ x ∈ G, ∀ r : ℝ, 0 < r →
    intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ Metric.closedBall 0 r) ≤
      ENNReal.ofReal (1 / 8) * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r)
  small_ball : ∀ x ∈ H, intrinsicRootKernel hij μ hfree x (Metric.closedBall 0 ρ) < 1 / 2
  source_measurable : MeasurableSet Z
  source_positive : μ Z ≠ 0
  source_regular : ∀ z ∈ Z, RootLeafRegular hij μ hfree z
  source_covariance : ∀ z ∈ Z, ∀ᵐ t : ℝ ∂volume, RootPairLeafCovariance hij μ hfree z t
  source_returns : ∀ z ∈ Z, ∀ T : ℝ, 1 ≤ T →
    volume.real (Ioc 0 T ∩ {t | rightAction z (rootPairFlow i j (-t)) ∉ G}) ≤ (1 / 100) * T ∧
    volume.real (Ioc 0 T ∩ {t | rightAction z (rootPairFlow i j (-t)) ∉ H}) ≤ (1 / 100) * T

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PositiveRootCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup
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

/-- The explicit root-times-remainder coordinates used in the
positive-root product induction. -/
def positiveRootFactorHomeomorph {n : ℕ} (S : Finset (Fin n × Fin n))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin n, (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin n} (hab : a ≠ b) (habS : (a, b) ∈ S)
    (herase : ∀ i j k : Fin n, (i, j) ∈ S.erase (a, b) →
      (j, k) ∈ S.erase (a, b) → (i, k) ∈ S.erase (a, b)) :
    (ℝ × positiveRootGeneratedGroup (S.erase (a, b))) ≃ₜ positiveRootGeneratedGroup S where
  toFun z := ⟨Matrix.SpecialLinearGroup.transvection hab z.1 * z.2.val,
    (positiveRootGeneratedGroup S).mul_mem
      (transvection_mem_positiveRootGeneratedGroup S hab habS z.1)
      (positiveRootGeneratedGroup_mono (Finset.erase_subset (a, b) S) z.2.prop)⟩
  invFun g := (g.val.val a b,
    ⟨Matrix.SpecialLinearGroup.transvection hab (-g.val.val a b) * g.val,
      positiveRootPattern_mem_generated (S.erase (a, b))
        (fun p hp => hpos p (Finset.mem_of_mem_erase hp)) herase
        (positiveRootPattern_eliminate S hpos hcomp hab habS g.val
          (positiveRootGeneratedGroup_pattern S hcomp g.prop))⟩)
  left_inv := by
    rintro ⟨t, w⟩
    have hw := remaining_root_entry S hpos hab herase w
    have ht : (Matrix.SpecialLinearGroup.transvection hab t * w.val).val a b = t := by
      rw [transvection_mul_root_entry, hw.1, hw.2, mul_one, zero_add]
    apply Prod.ext
    · exact ht
    · apply Subtype.ext
      change Matrix.SpecialLinearGroup.transvection hab
          (-(Matrix.SpecialLinearGroup.transvection hab t * w.val).val a b) *
        (Matrix.SpecialLinearGroup.transvection hab t * w.val) = w.val
      rw [ht, ← mul_assoc, ← Matrix.SpecialLinearGroup.transvection_add, neg_add_cancel]
      simp only [Matrix.SpecialLinearGroup.transvection_coeff_zero, one_mul]
  right_inv := by
    intro g
    apply Subtype.ext
    change Matrix.SpecialLinearGroup.transvection hab (g.val.val a b) *
      (Matrix.SpecialLinearGroup.transvection hab (-g.val.val a b) * g.val) = g.val
    rw [← mul_assoc, Matrix.SpecialLinearGroup.transvection_mul_neg, one_mul]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_rootTransvection hab).comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have hc : Continuous (fun g : positiveRootGeneratedGroup S => g.val.val a b) := by
      fun_prop
    exact hc.prodMk (Continuous.subtype_mk
      (((continuous_rootTransvection hab).comp hc.neg).mul continuous_subtype_val) _)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinates with the processed roots before the remaining subgroup

These coordinates keep the remaining subgroup on the right, so its
fibers are actual right orbits at every step of the product induction.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace RootPrefixCoordinates
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {T : Type*} [TopologicalSpace T]

def empty (n : ℕ) : RootPrefixCoordinates n ∅ PUnit where
  base _ := 1
  equiv := {
    toFun z := ⟨z.2.val, by simpa only [Finset.sdiff_empty] using z.2.prop⟩
    invFun w := (PUnit.unit, ⟨w.val, by simpa only [Finset.sdiff_empty] using w.prop⟩)
    left_inv z := Prod.ext (Subsingleton.elim _ _) (Subtype.ext rfl)
    right_inv w := Subtype.ext rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_snd).subtype_mk _
    continuous_invFun := continuous_const.prodMk (continuous_subtype_val.subtype_mk _) }
  param_eq_mul _ _ := (one_mul _).symm

def groupParam (C : RootPrefixCoordinates n P T)
    (z : UpperRootTransverse n × (T × positiveRootGeneratedGroup (allPositiveRoots n \ P))) : G n :=
  upperRootParam n (z.1, (upperRootWordHomeomorph n).symm (C.equiv z.2))

lemma groupParam_eq_mul (C : RootPrefixCoordinates n P T)
    (z : UpperRootTransverse n × (T × positiveRootGeneratedGroup (allPositiveRoots n \ P))) :
    C.groupParam z = z.1.val * (C.base z.2.1 * z.2.2.val) := by
  rw [groupParam, upperRootParam_eq_mul]
  have H := congrArg Subtype.val ((upperRootWordHomeomorph n).apply_symm_apply (C.equiv z.2))
  rw [← C.param_eq_mul]
  exact congrArg (z.1.val * ·) H

theorem groupParam_isOpenEmbedding (C : RootPrefixCoordinates n P T) :
    Topology.IsOpenEmbedding C.groupParam := by
  let E := (Homeomorph.refl (UpperRootTransverse n)).prodCongr
    (C.equiv.trans (upperRootWordHomeomorph n).symm)
  exact (upperRootParam_isOpenEmbedding n).comp E.isOpenEmbedding

def quotientParam (C : RootPrefixCoordinates n P T) (g : G n)
    (z : UpperRootTransverse n × (T × positiveRootGeneratedGroup (allPositiveRoots n \ P))) : X n :=
  Quotient.mk _ (g * C.groupParam z)

lemma quotientParam_eq_action (C : RootPrefixCoordinates n P T) (g : G n)
    (s : UpperRootTransverse n) (t : T)
    (w : positiveRootGeneratedGroup (allPositiveRoots n \ P)) :
    C.quotientParam g (s,(t,w)) =
      rightAction (Quotient.mk _ ((g * s.val) * C.base t)) w.val := by
  change Quotient.mk _ (g * C.groupParam (s,(t,w))) = _
  rw [C.groupParam_eq_mul]
  change Quotient.mk _ (g * (s.val * (C.base t * w.val))) =
    Quotient.mk _ (((g * s.val) * C.base t) * w.val)
  simp only [mul_assoc]

theorem quotientParam_localHomeomorph (C : RootPrefixCoordinates n P T) (g : G n) :
    IsLocalHomeomorph (C.quotientParam g) :=
  (quotient_covering n).isLocalHomeomorph.comp
    ((Homeomorph.mulLeft g).isLocalHomeomorph.comp C.groupParam_isOpenEmbedding.isLocalHomeomorph)

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixBoxes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual quotient boxes for every remaining root subgroup -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace RootPrefixCoordinates
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {T : Type*} [TopologicalSpace T]

def timeParam (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (g : G n)
    (z : (UpperRootTransverse n × T) × c.Time) : X n :=
  C.quotientParam g (z.1.1, (z.1.2, c.remainingWordHomeomorph hP hfinal z.2))

lemma timeParam_eq_action (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (g : G n)
    (z : (UpperRootTransverse n × T) × c.Time) :
    C.timeParam c hP hfinal g z =
      rightAction (Quotient.mk _ ((g * z.1.1.val) * C.base z.1.2)) (c.word z.2) :=
  C.quotientParam_eq_action g z.1.1 z.1.2 _

theorem timeParam_localHomeomorph (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (g : G n) :
    IsLocalHomeomorph (C.timeParam c hP hfinal g) := by
  let E := (Homeomorph.prodAssoc (UpperRootTransverse n) T c.Time).trans
    ((Homeomorph.refl (UpperRootTransverse n)).prodCongr
      ((Homeomorph.refl T).prodCongr (c.remainingWordHomeomorph hP hfinal)))
  exact (C.quotientParam_localHomeomorph g).comp E.isLocalHomeomorph

end RootPrefixCoordinates

structure RootPrefixBox {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (g : G n) where
  transverse : Set (UpperRootTransverse n × T)
  time : Set c.Time
  transverse_open : IsOpen transverse
  time_open : IsOpen time
  embedding : Topology.IsOpenEmbedding
    ((transverse ×ˢ time).domRestrict (C.timeParam c hP hfinal g))

namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
  {C : RootPrefixCoordinates n P T} {c : EliminationChain P D}
  {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

abbrev domain (B : RootPrefixBox C c hP hfinal g) := B.transverse ×ˢ B.time
abbrev param (B : RootPrefixBox C c hP hfinal g) :=
  B.domain.domRestrict (C.timeParam c hP hfinal g)
def range (B : RootPrefixBox C c hP hfinal g) := Set.range B.param

def coordinateMeasure (B : RootPrefixBox C c hP hfinal g) (μ : Measure (X n)) :
    Measure ((UpperRootTransverse n × T) × c.Time) :=
  (Measure.comap B.param μ).map Subtype.val

instance coordinateMeasure_finite (B : RootPrefixBox C c hP hfinal g) (μ : Measure (X n))
    [IsFiniteMeasure μ] : IsFiniteMeasure (B.coordinateMeasure μ) := by
  have he := B.embedding.measurableEmbedding
  have : IsFiniteMeasure (Measure.comap B.param μ) := ⟨by
    rw [he.comap_apply]
    exact lt_of_le_of_lt (measure_mono (subset_univ _)) (measure_lt_top μ univ)⟩
  unfold coordinateMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma map_coordinateMeasure (B : RootPrefixBox C c hP hfinal g) (μ : Measure (X n)) :
    (B.coordinateMeasure μ).map (C.timeParam c hP hfinal g) = μ.restrict B.range := by
  rw [coordinateMeasure,Measure.map_map]
  · exact B.embedding.measurableEmbedding.map_comap μ
  · exact (C.timeParam_localHomeomorph c hP hfinal g).continuous.measurable
  · exact measurable_subtype_coe

def conditionalKernel (B : RootPrefixBox C c hP hfinal g) (μ : Measure (X n))
    [IsFiniteMeasure μ] : Kernel (UpperRootTransverse n × T) c.Time :=
  (B.coordinateMeasure μ).condKernel

instance conditionalKernel_markov (B : RootPrefixBox C c hP hfinal g) (μ : Measure (X n))
    [IsFiniteMeasure μ] : IsMarkovKernel (B.conditionalKernel μ) := by
  unfold conditionalKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixRestrictions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient restrictions and null sets in the remaining-root quotient boxes -/

noncomputable section
open Matrix MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

theorem ae_coordinate_of_ambient (B : RootPrefixBox C c hP hfinal g)
    (μ : Measure (X n)) {Q : X n → Prop} (hQ : ∀ᵐ x ∂μ, Q x) :
    ∀ᵐ z ∂B.coordinateMeasure μ, Q (C.timeParam c hP hfinal g z) := by
  have h := (Measure.absolutelyContinuous_of_le (Measure.restrict_le_self :
    μ.restrict B.range ≤ μ)).ae_le hQ
  rw [←B.map_coordinateMeasure μ] at h
  exact ae_of_ae_map (C.timeParam_localHomeomorph c hP hfinal g).continuous.measurable.aemeasurable h

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supports of actual remaining-root conditional kernels -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

lemma coordinateMeasure_ae_domain (B : RootPrefixBox Pfx c hP hfinal g) (μ : Measure (X n)) :
    ∀ᵐ z ∂B.coordinateMeasure μ, z ∈ B.domain := by
  rw [coordinateMeasure]
  exact (ae_map_iff measurable_subtype_coe.aemeasurable
    (B.transverse_open.prod B.time_open).measurableSet).mpr
      (ae_of_all _ fun z => z.prop)

lemma coordinateMeasure_fst_ae_transverse (B : RootPrefixBox Pfx c hP hfinal g) (μ : Measure (X n)) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst, s ∈ B.transverse := by
  rw [Measure.fst]
  apply (ae_map_iff measurable_fst.aemeasurable B.transverse_open.measurableSet).mpr
  filter_upwards [B.coordinateMeasure_ae_domain μ] with z hz
  exact hz.1

lemma conditionalKernel_ae_time (B : RootPrefixBox Pfx c hP hfinal g) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst, ∀ᵐ t ∂B.conditionalKernel μ s, t ∈ B.time := by
  have H : ∀ᵐ z ∂((B.coordinateMeasure μ).fst ⊗ₘ B.conditionalKernel μ), z.2 ∈ B.time := by
    rw [conditionalKernel, Measure.disintegrate]
    filter_upwards [B.coordinateMeasure_ae_domain μ] with z hz
    exact hz.2
  exact Measure.ae_ae_of_ae_compProd H

lemma conditionalKernel_time_mass (B : RootPrefixBox Pfx c hP hfinal g) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst, B.conditionalKernel μ s B.time = 1 := by
  filter_upwards [B.conditionalKernel_ae_time μ] with s hs
  rw [← measure_univ (μ := B.conditionalKernel μ s)]
  exact measure_congr (ae_eq_univ.mpr hs)


end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixCompatibility
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible normalized restrictions of remaining-root box kernels -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

lemma coordinateMeasure_apply (B : RootPrefixBox Pfx c hP hfinal g) (μ : Measure (X n))
    {S : Set ((UpperRootTransverse n × T) × c.Time)} (hS : MeasurableSet S) :
    B.coordinateMeasure μ S =
      μ (Pfx.timeParam c hP hfinal g '' (S ∩ B.domain)) := by
  rw [coordinateMeasure,Measure.map_apply measurable_subtype_coe hS,
    B.embedding.measurableEmbedding.comap_apply]
  congr 1
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z.val,⟨hz,z.prop⟩,rfl⟩
  · rintro ⟨z,⟨hz,hzd⟩,rfl⟩
    exact ⟨⟨z,hzd⟩,hz,rfl⟩



def shrink (B : RootPrefixBox Pfx c hP hfinal g)
    (U : Set ((UpperRootTransverse n × T))) (V : Set (c.Time)) (hU : IsOpen U) (hV : IsOpen V)
    (hUB : U ⊆ B.transverse) (hVB : V ⊆ B.time) : RootPrefixBox Pfx c hP hfinal g :=
  ⟨U,V,hU,hV,B.embedding.comp (Topology.IsOpenEmbedding.inclusion
    (Set.prod_mono hUB hVB) ((hU.prod hV).preimage continuous_subtype_val))⟩



theorem shrink_coordinateMeasure (B : RootPrefixBox Pfx c hP hfinal g)
    (U : Set ((UpperRootTransverse n × T))) (V : Set (c.Time)) (hU : IsOpen U) (hV : IsOpen V)
    (hUB : U ⊆ B.transverse) (hVB : V ⊆ B.time) (μ : Measure (X n)) :
    (B.shrink U V hU hV hUB hVB).coordinateMeasure μ =
      (B.coordinateMeasure μ).restrict (U ×ˢ V) := by
  ext S hS
  rw [Measure.restrict_apply hS,coordinateMeasure_apply _ μ hS,
    coordinateMeasure_apply _ μ (hS.inter (hU.measurableSet.prod hV.measurableSet))]
  congr 2
  change S ∩ U ×ˢ V = (S ∩ U ×ˢ V) ∩ B.domain
  exact (Set.inter_eq_left.mpr ((Set.inter_subset_right).trans (Set.prod_mono hUB hVB))).symm



theorem shrink_conditionalKernel (B : RootPrefixBox Pfx c hP hfinal g)
    (U : Set ((UpperRootTransverse n × T))) (V : Set (c.Time)) (hU : IsOpen U) (hV : IsOpen V)
    (hUB : U ⊆ B.transverse) (hVB : V ⊆ B.time) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst.restrict U,
      B.conditionalKernel μ s V •
        (B.shrink U V hU hV hUB hVB).conditionalKernel μ s =
          (B.conditionalKernel μ s).restrict V := by
  simp only [conditionalKernel,shrink_coordinateMeasure]
  exact restricted_conditional_kernel _ hU.measurableSet hV.measurableSet



theorem shrink_marginal (B : RootPrefixBox Pfx c hP hfinal g)
    (U : Set ((UpperRootTransverse n × T))) (V : Set (c.Time)) (hU : IsOpen U) (hV : IsOpen V)
    (hUB : U ⊆ B.transverse) (hVB : V ⊆ B.time) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ((B.shrink U V hU hV hUB hVB).coordinateMeasure μ).fst =
      ((B.coordinateMeasure μ).fst.restrict U).withDensity
        (fun s => B.conditionalKernel μ s V) := by
  rw [shrink_coordinateMeasure,restricted_conditional_marginal _ hU.measurableSet hV.measurableSet]
  rfl

lemma shrink_marginal_absolutelyContinuous (B : RootPrefixBox Pfx c hP hfinal g)
    (U : Set ((UpperRootTransverse n × T))) (J : Set (c.Time)) (hU : IsOpen U) (hJ : IsOpen J)
    (hUB : U ⊆ B.transverse) (hJB : J ⊆ B.time) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ((B.shrink U J hU hJ hUB hJB).coordinateMeasure μ).fst ≪
      (B.coordinateMeasure μ).fst.restrict U := by
  rw [shrink_marginal]
  exact withDensity_absolutelyContinuous _ _

lemma shrink_marginal_ae_anchor_pos (B : RootPrefixBox Pfx c hP hfinal g)
    (U : Set ((UpperRootTransverse n × T))) (J : Set (c.Time)) (hU : IsOpen U) (hJ : IsOpen J)
    (hUB : U ⊆ B.transverse) (hJB : J ⊆ B.time) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂((B.shrink U J hU hJ hUB hJB).coordinateMeasure μ).fst,
      B.conditionalKernel μ s J ≠ 0 := by
  rw [shrink_marginal]
  exact (ae_withDensity_iff (B.conditionalKernel μ |>.measurable_coe hJ.measurableSet)).mpr
    (ae_of_all _ fun _ h => h)



theorem overlap_anchorNormalize (B C : RootPrefixBox Pfx c hP hfinal g)
    (U : Set ((UpperRootTransverse n × T))) (J : Set (c.Time)) (hU : IsOpen U) (hJ : IsOpen J)
    (hUB : U ⊆ B.transverse) (hUC : U ⊆ C.transverse)
    (hJB : J ⊆ B.time) (hJC : J ⊆ C.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂((B.shrink U J hU hJ hUB hJB).coordinateMeasure μ).fst,
      B.conditionalKernel μ s J ≠ 0 ∧ C.conditionalKernel μ s J ≠ 0 ∧
      (anchorNormalize (B.conditionalKernel μ s) J).restrict (B.time ∩ C.time) =
        (anchorNormalize (C.conditionalKernel μ s) J).restrict (B.time ∩ C.time) := by
  let V := B.time ∩ C.time
  have hV : IsOpen V := B.time_open.inter C.time_open
  let D := B.shrink U V hU hV hUB inter_subset_left
  have hD : D = C.shrink U V hU hV hUC inter_subset_right := rfl
  have hA : B.shrink U J hU hJ hUB hJB = C.shrink U J hU hJ hUC hJC := rfl
  have hB := (B.shrink_marginal_absolutelyContinuous U J hU hJ hUB hJB μ).ae_le
    (B.shrink_conditionalKernel U V hU hV hUB inter_subset_left μ)
  have hC := (C.shrink_marginal_absolutelyContinuous U J hU hJ hUC hJC μ).ae_le
    (C.shrink_conditionalKernel U V hU hV hUC inter_subset_right μ)
  rw [←hA] at hC
  have hpB := B.shrink_marginal_ae_anchor_pos U J hU hJ hUB hJB μ
  have hpC := C.shrink_marginal_ae_anchor_pos U J hU hJ hUC hJC μ
  rw [←hA] at hpC
  filter_upwards [hB,hC,hpB,hpC] with s hsB hsC hpB hpC
  have hJV : J ⊆ V := subset_inter hJB hJC
  have H₁ := (anchorNormalize_restrict _ _ hJ.measurableSet hJV hsB hpB).2
  have H₂ := (anchorNormalize_restrict _ _ hJ.measurableSet hJV hsC hpC).2
  refine ⟨hpB,hpC,?_⟩
  exact H₁.symm.trans H₂


lemma shrink_full_time_marginal (B : RootPrefixBox Pfx c hP hfinal g)
    (U : Set ((UpperRootTransverse n × T))) (hU : IsOpen U) (hUB : U ⊆ B.transverse)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ((B.shrink U B.time hU B.time_open hUB subset_rfl).coordinateMeasure μ).fst =
      (B.coordinateMeasure μ).fst.restrict U := by
  rw [shrink_marginal]
  calc
    _ = ((B.coordinateMeasure μ).fst.restrict U).withDensity 1 := by
      apply withDensity_congr_ae
      exact ae_restrict_of_ae (B.conditionalKernel_time_mass μ)
    _ = _ := withDensity_one

theorem base_overlap_anchorNormalize (A B C : RootPrefixBox Pfx c hP hfinal g)
    (hAB : A.time ⊆ B.time) (hAC : A.time ⊆ C.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      s ∈ B.transverse → s ∈ C.transverse →
      B.conditionalKernel μ s A.time ≠ 0 ∧ C.conditionalKernel μ s A.time ≠ 0 ∧
      (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (B.time ∩ C.time) =
        (anchorNormalize (C.conditionalKernel μ s) A.time).restrict (B.time ∩ C.time) := by
  let U := A.transverse ∩ B.transverse ∩ C.transverse
  have hU : IsOpen U := (A.transverse_open.inter B.transverse_open).inter C.transverse_open
  have hUA : U ⊆ A.transverse := inter_subset_left.trans inter_subset_left
  have hUB : U ⊆ B.transverse := inter_subset_left.trans inter_subset_right
  have hUC : U ⊆ C.transverse := inter_subset_right
  have H := overlap_anchorNormalize B C U A.time hU A.time_open hUB hUC hAB hAC μ
  have hD : B.shrink U A.time hU A.time_open hUB hAB =
      A.shrink U A.time hU A.time_open hUA subset_rfl := rfl
  rw [hD,A.shrink_full_time_marginal] at H
  have H' := (ae_restrict_iff' hU.measurableSet).mp H
  filter_upwards [H',A.coordinateMeasure_fst_ae_transverse μ] with s hs hsA
  intro hsB hsC
  exact hs ⟨⟨hsA,hsB⟩,hsC⟩



theorem base_anchor_restrict (A B : RootPrefixBox Pfx c hP hfinal g) (hAB : A.time ⊆ B.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ B.transverse →
      B.conditionalKernel μ s A.time ≠ 0 ∧
      (anchorNormalize (B.conditionalKernel μ s) A.time).restrict A.time =
        A.conditionalKernel μ s := by
  filter_upwards [base_overlap_anchorNormalize A A B subset_rfl hAB μ,
    A.coordinateMeasure_fst_ae_transverse μ,A.conditionalKernel_time_mass μ,
    A.conditionalKernel_ae_time μ] with s hs hsA hm ht
  intro hsB
  have H := hs hsA hsB
  refine ⟨H.2.1,?_⟩
  rw [inter_eq_left.mpr hAB] at H
  rw [←H.2.2]
  have hn : anchorNormalize (A.conditionalKernel μ s) A.time = A.conditionalKernel μ s := by
    simp only [anchorNormalize,hm,inv_one,one_smul]
  rw [hn]
  exact Measure.restrict_eq_self_of_ae_mem ht


end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixLongBoxes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact remaining-root time sets fit in actual prefix quotient boxes -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (g : G n)

lemma timeParam_injective_of_free (s : UpperRootTransverse n × T)
    (hfree : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction (Quotient.mk _ ((g*s.1.val)*C.base s.2)) v =
        Quotient.mk _ ((g*s.1.val)*C.base s.2) → v = 1) :
    Function.Injective (fun t => C.timeParam c hP hfinal g (s,t)) := by
  intro t u h
  let wt := c.word t
  let wu := c.word u
  have htw : wt ∈ positiveRootGeneratedGroup (allPositiveRoots n) :=
    positiveRootGeneratedGroup_mono Finset.sdiff_subset (c.word_mem_remaining hfinal t)
  have huw : wu ∈ positiveRootGeneratedGroup (allPositiveRoots n) :=
    positiveRootGeneratedGroup_mono Finset.sdiff_subset (c.word_mem_remaining hfinal u)
  have hh := congrArg (fun x => rightAction x wu⁻¹) h
  change rightAction (C.timeParam c hP hfinal g (s,t)) wu⁻¹ =
    rightAction (C.timeParam c hP hfinal g (s,u)) wu⁻¹ at hh
  rw [C.timeParam_eq_action,C.timeParam_eq_action,rightAction_mul,rightAction_mul] at hh
  have hz : rightAction (Quotient.mk _ ((g*s.1.val)*C.base s.2)) (wt*wu⁻¹) =
      Quotient.mk _ ((g*s.1.val)*C.base s.2) := by
    simpa only [wt,wu,mul_inv_cancel,rightAction_one] using hh
  have he := hfree (wt*wu⁻¹)
    ((positiveRootGeneratedGroup _).mul_mem htw ((positiveRootGeneratedGroup _).inv_mem huw)) hz
  apply (c.word_isEmbedding_remaining hfinal).injective
  exact mul_right_cancel (show wt*wu⁻¹=wu*wu⁻¹ from he.trans (mul_inv_cancel wu).symm)

theorem box_contains_compact_time (s : UpperRootTransverse n × T)
    (hinj : Function.Injective (fun t => C.timeParam c hP hfinal g (s,t)))
    (K : Set c.Time) (hK : IsCompact K) :
    ∃ B : RootPrefixBox C c hP hfinal g, s ∈ B.transverse ∧ K ⊆ B.time := by
  have hf := C.timeParam_localHomeomorph c hP hfinal g
  have hi : Set.InjOn (C.timeParam c hP hfinal g) ({s} ×ˢ K) := by
    rintro ⟨s₁,t₁⟩ ⟨hs₁,_⟩ ⟨s₂,t₂⟩ ⟨hs₂,_⟩ heq
    have h₁ : s₁=s := hs₁
    have h₂ : s₂=s := hs₂
    subst s₁
    subst s₂
    exact Prod.ext rfl (hinj heq)
  obtain ⟨W,hW,hKW,hemb⟩ := compact_injective_localHomeomorph_neighborhood hf
    (isCompact_singleton.prod hK) hi
  obtain ⟨U,V,hU,hV,hsU,hKV,hUV⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({s} : Set (UpperRootTransverse n × T))) hK hW hKW
  have he := hemb.comp (Topology.IsOpenEmbedding.inclusion hUV
    ((hU.prod hV).preimage continuous_subtype_val))
  exact ⟨⟨U,V,hU,hV,he⟩,hsU (Set.mem_singleton s),hKV⟩

end RootPrefixCoordinates
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

theorem ae_injective_slice_of_ae_free (B : RootPrefixBox C c hP hfinal g)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      Function.Injective (fun t => C.timeParam c hP hfinal g (s,t)) := by
  have hf := B.ae_coordinate_of_ambient μ hfree
  have hf' : ∀ᵐ z ∂((B.coordinateMeasure μ).fst ⊗ₘ B.conditionalKernel μ),
      ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
        rightAction (C.timeParam c hP hfinal g z) v = C.timeParam c hP hfinal g z → v = 1 := by
    simpa only [conditionalKernel,Measure.disintegrate] using hf
  have H := Measure.ae_ae_of_ae_compProd hf'
  filter_upwards [H] with s hs
  obtain ⟨t,ht⟩ := hs.exists
  apply C.timeParam_injective_of_free c hP hfinal g s
  apply subgroup_free_of_free_translate (positiveRootGeneratedGroup (allPositiveRoots n))
    (Quotient.mk _ ((g*s.1.val)*C.base s.2)) (c.word t)
    (positiveRootGeneratedGroup_mono Finset.sdiff_subset (c.word_mem_remaining hfinal t))
  simpa only [C.timeParam_eq_action] using ht

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixWindows
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable long-box exhaustions for each remaining subgroup -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

namespace RootPrefixCoordinates
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (g : G n)

theorem exists_countable_boxes_exact_time (R : ℝ) :
    ∃ F : Set (RootPrefixBox C c hP hfinal g), F.Countable ∧
      (∀ B ∈ F, B.time = c.cube R) ∧
      ∀ s : UpperRootTransverse n × T,
        Function.Injective (fun t => C.timeParam c hP hfinal g (s,t)) →
        ∃ B ∈ F, s ∈ B.transverse := by
  let Good := {B : RootPrefixBox C c hP hfinal g | B.time = c.cube R}
  obtain ⟨F,hFG,hFc,hF⟩ := isOpen_biUnion_countable Good
    (fun B : RootPrefixBox C c hP hfinal g => B.transverse) (fun B _ => B.transverse_open)
  refine ⟨F,hFc,fun B hB => hFG hB,?_⟩
  intro s hs
  obtain ⟨B,hsB,hKB⟩ := C.box_contains_compact_time c hP hfinal g s hs
    (c.closedCube R) (c.closedCube_compact R)
  let E := B.shrink B.transverse (c.cube R) B.transverse_open (c.cube_open R)
    subset_rfl ((c.cube_subset_closedCube R).trans hKB)
  have hE : E ∈ Good := rfl
  have H : s ∈ ⋃ B ∈ Good, B.transverse := mem_iUnion.mpr ⟨E,mem_iUnion.mpr ⟨hE,hsB⟩⟩
  rw [←hF] at H
  simpa only [mem_iUnion,exists_prop] using H

def longBoxFamily (R : ℝ) (m : ℕ) : Set (RootPrefixBox C c hP hfinal g) :=
  (C.exists_countable_boxes_exact_time c hP hfinal g (R+m)).choose

lemma longBoxFamily_countable (R : ℝ) (m : ℕ) :
    (C.longBoxFamily c hP hfinal g R m).Countable :=
  (C.exists_countable_boxes_exact_time c hP hfinal g (R+m)).choose_spec.1

lemma longBoxFamily_time (R : ℝ) (m : ℕ)
    (B : RootPrefixBox C c hP hfinal g) (hB : B ∈ C.longBoxFamily c hP hfinal g R m) :
    B.time = c.cube (R+m) :=
  (C.exists_countable_boxes_exact_time c hP hfinal g (R+m)).choose_spec.2.1 B hB

lemma longBoxFamily_covers (R : ℝ) (m : ℕ) (s : UpperRootTransverse n × T)
    (hs : Function.Injective (fun t => C.timeParam c hP hfinal g (s,t))) :
    ∃ B ∈ C.longBoxFamily c hP hfinal g R m, s ∈ B.transverse :=
  (C.exists_countable_boxes_exact_time c hP hfinal g (R+m)).choose_spec.2.2 s hs

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixLeafMeasure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Locally finite leaf measures on each remaining subgroup

The actual prefix-box kernels glue through their normalized restrictions
on a countable long-box exhaustion. No root-product identity is assumed.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

theorem ae_exists_prefixLeafMeasure (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∃ ν : Measure (c.Time),
      IsLocallyFiniteMeasure ν ∧ ν A.time = 1 ∧
      ν.restrict A.time = A.conditionalKernel μ s ∧
      ∀ (m : ℕ) (B : RootPrefixBox Pfx c hP hfinal g), B ∈ Pfx.longBoxFamily c hP hfinal g R m →
        s ∈ B.transverse →
        ν.restrict (c.remainingWindow R m) =
          (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (c.remainingWindow R m) := by
  let C := Pfx.longBoxFamily c hP hfinal g R
  have hCc (m : ℕ) : (C m).Countable := Pfx.longBoxFamily_countable c hP hfinal g R m
  let (m : ℕ) : Countable (C m) := (hCc m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = c.remainingWindow R m :=
    Pfx.longBoxFamily_time c hP hfinal g R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (c.remainingWindow_mono R (Nat.zero_le m))
  have hp : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      ∀ (a b : ℕ) (B : C a) (D : C b), s ∈ B.val.transverse → s ∈ D.val.transverse →
        B.val.conditionalKernel μ s A.time ≠ 0 ∧ D.val.conditionalKernel μ s A.time ≠ 0 ∧
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict (B.val.time ∩ D.val.time) =
          (anchorNormalize (D.val.conditionalKernel μ s) A.time).restrict (B.val.time ∩ D.val.time) := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    apply ae_all_iff.mpr
    intro B
    apply ae_all_iff.mpr
    intro D
    exact base_overlap_anchorNormalize A B.val D.val (hinc a B) (hinc b D) μ
  have ha : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      ∀ (m : ℕ) (B : C m), s ∈ B.val.transverse →
        B.val.conditionalKernel μ s A.time ≠ 0 ∧
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict A.time =
          A.conditionalKernel μ s := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    exact base_anchor_restrict A B.val (hinc m B) μ
  filter_upwards [A.ae_injective_slice_of_ae_free μ hfree,hp,ha] with s hs hp ha
  have hcover (m : ℕ) : ∃ B : C m, s ∈ B.val.transverse := by
    obtain ⟨B,hB,hsB⟩ := Pfx.longBoxFamily_covers c hP hfinal g R m s hs
    exact ⟨⟨B,hB⟩,hsB⟩
  choose B hB using hcover
  let N (m : ℕ) : Measure (c.Time) :=
    (anchorNormalize ((B m).val.conditionalKernel μ s) A.time).restrict (c.remainingWindow R m)
  have hpos (m : ℕ) : (B m).val.conditionalKernel μ s A.time ≠ 0 := (ha m (B m) (hB m)).1
  let (m : ℕ) : IsFiniteMeasure (anchorNormalize ((B m).val.conditionalKernel μ s) A.time) :=
    anchorNormalize_finite _ _ (hpos m)
  let (m : ℕ) : IsFiniteMeasure (N m) := by dsimp [N]; infer_instance
  have hc : ∀ a b, a ≤ b → (N b).restrict (c.remainingWindow R a) = N a := by
    intro a b hab
    have H := (hp a b (B a) (B b) (hB a) (hB b)).2.2
    rw [hT a (B a),hT b (B b),inter_eq_left.mpr (c.remainingWindow_mono R hab)] at H
    dsimp [N]
    rw [Measure.restrict_restrict (c.remainingWindow_open R a).measurableSet,
      inter_eq_left.mpr (c.remainingWindow_mono R hab)]
    exact H.symm
  let ν := increasingMeasureLimit N (restrictionChain_monotone N (c.remainingWindow R) hc)
  have hν (m : ℕ) : ν.restrict (c.remainingWindow R m) = N m :=
    increasingMeasureLimit_restrict N (c.remainingWindow R)
      (fun m => (c.remainingWindow_open R m).measurableSet) hc m
  have hνA : ν.restrict A.time = A.conditionalKernel μ s := by
    have H := congrArg (fun ξ : Measure (c.Time) => ξ.restrict A.time) (hν 0)
    dsimp [N] at H
    rw [Measure.restrict_restrict A.time_open.measurableSet,inter_eq_left.mpr hAR,
      Measure.restrict_restrict A.time_open.measurableSet,inter_eq_left.mpr hAR] at H
    exact H.trans (ha 0 (B 0) (hB 0)).2
  refine ⟨ν,increasingMeasureLimit_locallyFinite N (c.remainingWindow R)
    (c.remainingWindow_open R) (fun m => (c.remainingWindow_open R m).measurableSet)
    (c.remainingWindow_cover R) hc,?_,hνA,?_⟩
  · have H := congrArg (fun ξ : Measure (c.Time) => ξ univ) hνA
    simpa only [Measure.restrict_apply MeasurableSet.univ,univ_inter,measure_univ] using H
  · intro m D hD hsD
    let D' : C m := ⟨D,hD⟩
    have H := (hp m m (B m) D' (hB m) hsD).2.2
    rw [hT m (B m),hT m D',inter_self] at H
    exact (hν m).trans H



end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixNormalizedLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized remaining-subgroup leaf measures

The chosen measure is characterized by actual prefix-box conditionals,
and is independent of the exhaustion radius.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology Classical
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

def IsNormalizedPrefixLeaf (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : (UpperRootTransverse n × T)) (ν : Measure (c.Time)) : Prop :=
  IsLocallyFiniteMeasure ν ∧ ν A.time = 1 ∧
    ν.restrict A.time = A.conditionalKernel μ s ∧
    ∀ (m : ℕ) (B : RootPrefixBox Pfx c hP hfinal g), B ∈ Pfx.longBoxFamily c hP hfinal g R m →
      s ∈ B.transverse → ν.restrict (c.remainingWindow R m) =
        (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (c.remainingWindow R m)



def leafMeasure (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : (UpperRootTransverse n × T)) : Measure (c.Time) :=
  if h : ∃ ν : Measure (c.Time), A.IsNormalizedPrefixLeaf R μ s ν then h.choose else 0

lemma leafMeasure_spec_of_exists (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : (UpperRootTransverse n × T))
    (h : ∃ ν, A.IsNormalizedPrefixLeaf R μ s ν) :
    A.IsNormalizedPrefixLeaf R μ s (A.leafMeasure R μ s) := by
  simpa only [leafMeasure,dite_eq_left h] using h.choose_spec


theorem ae_leafMeasure_spec (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      A.IsNormalizedPrefixLeaf R μ s (A.leafMeasure R μ s) := by
  filter_upwards [A.ae_exists_prefixLeafMeasure R hAR μ hfree] with s hs
  exact A.leafMeasure_spec_of_exists R μ s hs



end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixLeafKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Measurable remaining-subgroup leaf kernels

The chosen leaf measure is measurable almost everywhere because its
restrictions to the countable exhausting windows are actual normalized
conditional kernels. This supplies a measurable kernel for integration.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

lemma aemeasurable_leafMeasure_restrict_window (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1)
    (m : ℕ) :
    AEMeasurable (fun s => (A.leafMeasure R μ s).restrict (c.remainingWindow R m))
      (A.coordinateMeasure μ).fst := by
  let C := Pfx.longBoxFamily c hP hfinal g R
  let : Countable (C m) := (Pfx.longBoxFamily_countable c hP hfinal g R m).to_subtype
  let U := ⋃ B : C m, B.val.transverse
  have hU : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ U := by
    filter_upwards [A.ae_injective_slice_of_ae_free μ hfree] with s hs
    obtain ⟨B,hB,hsB⟩ := Pfx.longBoxFamily_covers c hP hfinal g R m s hs
    exact mem_iUnion.mpr ⟨⟨B,hB⟩,hsB⟩
  have H : AEMeasurable (fun s => (A.leafMeasure R μ s).restrict (c.remainingWindow R m))
      ((A.coordinateMeasure μ).fst.restrict U) := by
    apply aemeasurable_iUnion_iff.mpr
    intro B
    have hM : Measurable (fun s =>
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict (c.remainingWindow R m)) := by
      apply Measure.measurable_of_measurable_coe
      intro T hT
      simp only [Measure.restrict_apply hT,anchorNormalize,Measure.smul_apply,smul_eq_mul]
      exact ((B.val.conditionalKernel μ).measurable_coe A.time_open.measurableSet).inv.mul
        ((B.val.conditionalKernel μ).measurable_coe (hT.inter (c.remainingWindow_open R m).measurableSet))
    apply hM.aemeasurable.congr
    change ∀ᵐ s ∂(A.coordinateMeasure μ).fst.restrict B.val.transverse, _
    rw [ae_restrict_iff' B.val.transverse_open.measurableSet]
    filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree] with s hs
    intro hsB
    exact (hs.2.2.2 m B.val B.prop hsB).symm
  simpa only [Measure.restrict_eq_self_of_ae_mem hU] using H



theorem aemeasurable_leafMeasure (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    AEMeasurable (A.leafMeasure R μ) (A.coordinateMeasure μ).fst := by
  let W := c.remainingWindow R
  let V := disjointed W
  have hV (m : ℕ) : MeasurableSet (V m) :=
    MeasurableSet.disjointed (fun m => (c.remainingWindow_open R m).measurableSet) m
  have hM (m : ℕ) : AEMeasurable
      (fun s => (A.leafMeasure R μ s).restrict (V m)) (A.coordinateMeasure μ).fst := by
    have H := (measurable_measure_restrict (hV m)).comp_aemeasurable
      (A.aemeasurable_leafMeasure_restrict_window R hAR μ hfree m)
    change AEMeasurable (fun s => ((A.leafMeasure R μ s).restrict (W m)).restrict (V m))
      (A.coordinateMeasure μ).fst at H
    have hVW : V m ∩ W m = V m := inter_eq_left.mpr (disjointed_subset W m)
    simpa only [Measure.restrict_restrict (hV m),hVW] using H
  have hE (s : (UpperRootTransverse n × T)) : A.leafMeasure R μ s =
      Measure.sum (fun m => (A.leafMeasure R μ s).restrict (V m)) := by
    exact measure_eq_sum_disjointed (A.leafMeasure R μ s) W
      (fun m => (c.remainingWindow_open R m).measurableSet) (c.remainingWindow_cover R)
  exact (measurable_measure_sum.comp_aemeasurable (aemeasurable_pi_iff.mpr hM)).congr
    (ae_of_all _ fun s => (hE s).symm)



def leafKernel (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    Kernel ((UpperRootTransverse n × T)) (c.Time) where
  toFun := (A.aemeasurable_leafMeasure R hAR μ hfree).mk (A.leafMeasure R μ)
  measurable' := (A.aemeasurable_leafMeasure R hAR μ hfree).measurable_mk


end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixRegularKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Everywhere locally finite versions of remaining-subgroup kernels -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal Classical

namespace DukePrimeDegree
open PrimeDegreePackets

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def finiteRemainingCubes {S : Type*} [MeasurableSpace S] (c : EliminationChain P D)
    (κ : Kernel S (c.Time)) : Set S :=
  {s | ∀ m : ℕ, κ s (c.closedCube m) < ∞}

lemma measurableSet_finiteRemainingCubes {S : Type*} [MeasurableSpace S] (c : EliminationChain P D)
    (κ : Kernel S (c.Time)) : MeasurableSet (finiteRemainingCubes c κ) := by
  change MeasurableSet {s | ∀ m : ℕ, κ s (c.closedCube m) < ∞}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun m => measurableSet_lt
    (κ.measurable_coe (c.closedCube_compact m).measurableSet) measurable_const)

def locallyFiniteRemainingVersion {S : Type*} [MeasurableSpace S] (c : EliminationChain P D)
    (κ : Kernel S (c.Time)) : Kernel S (c.Time) :=
  Kernel.piecewise (measurableSet_finiteRemainingCubes c κ) κ 0

namespace RootPrefixBox
variable {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

def regularLeafKernel (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) : Kernel ((UpperRootTransverse n × T)) (c.Time) :=
  locallyFiniteRemainingVersion c (A.leafKernel R hAR μ hfree)

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixBasedMeasure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable remaining-subgroup leaves based at the sampled point -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

def basedLeaf (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (z : (UpperRootTransverse n × T) × c.Time) : Measure c.Time :=
  c.basedRemainingMeasure hP hfinal (A.leafMeasure R μ z.1) z.2

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_WholeFutureCountableCover
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A countable family of boxes containing complete future fibers

The family is chosen before the sample. Bounded future fibers, transported
to the sampled coordinates, fit into one member of this fixed family.
This is the countability needed for gluing the local future laws.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]

def wholeFutureBoxFamily (C : RootPrefixCoordinates n P V) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n) (g : G n) :
    Set (RootPrefixBox C c hP hf g) := ⋃ m : ℕ, C.longBoxFamily c hP hf g 1 m

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootFactorTransversal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

theorem root_transversal_isOpenEmbedding {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    {A : Type*} [TopologicalSpace A] (f : A → RootPivot a k) (hf : Continuous f)
    (hchart : Topology.IsOpenEmbedding
      (fun z : A × ℝ => rootPivotTranslate hab (f z.1) z.2)) :
    Topology.IsOpenEmbedding (fun x => rootSliceRepresentative hab (f x)) := by
  let τ : A → ℝ := fun x => -rootParameter a b k (f x).val
  have hτ : Continuous τ := (continuous_rootParameter.comp hf).neg
  let H := (rootPivotHomeomorph hab).isOpenEmbedding.comp
    (hchart.comp (fiberShear (Homeomorph.refl A) τ hτ).isOpenEmbedding)
  have he : Topology.IsOpenEmbedding
      (Prod.map (fun x => rootSliceRepresentative hab (f x)) (id : ℝ → ℝ)) := by
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    rw [Function.comp_apply, Function.comp_apply, rootPivotHomeomorph_translate]
    apply Prod.ext
    · rfl
    · change z.2 = rootParameter a b k (f z.1).val +
        (z.2 + -rootParameter a b k (f z.1).val)
      ring
  exact isOpenEmbedding_of_prodMap_real he

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixFactorChart
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual one-root transversals inside every remaining-group chart -/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace RootPrefixCoordinates
variable {n : ℕ} (s : InitialRootStep n) {T : Type*} [TopologicalSpace T]
  (C : RootPrefixCoordinates n s.processed T) (g : G n)

lemma factorSlice_param (k : Fin n) (z : C.factorPivotDomain s g k) (t : ℝ) :
    rootQuotientParametrization s.distinct (C.factorSlice s g k z,t) =
      Quotient.mk _ (C.factorBase s g z.val * Matrix.SpecialLinearGroup.transvection s.distinct
        (t - rootParameter s.root.1 s.root.2 k (C.factorBase s g z.val))) := by
  change Quotient.mk _ ((C.factorBase s g z.val *
    Matrix.SpecialLinearGroup.transvection s.distinct
      (-rootParameter s.root.1 s.root.2 k (C.factorBase s g z.val))) *
      Matrix.SpecialLinearGroup.transvection s.distinct t) = _
  rw [mul_assoc, ← Matrix.SpecialLinearGroup.transvection_add]
  congr 3
  ring

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ShiftedRootLeafHolonomy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projective root-leaf comparison with different coordinate origins -/

noncomputable section
open Matrix MeasureTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace RootPrefixCoordinates
variable {n : ℕ} (s : InitialRootStep n) {T : Type*} [TopologicalSpace T]
  (C : RootPrefixCoordinates n s.processed T) (g : G n)

lemma factorSlice_orbit (k : Fin n) (z : C.factorPivotDomain s g k) (t : ℝ) :
    rootQuotientParametrization s.distinct (C.factorSlice s g k z,t) =
      rightAction (Quotient.mk _ ((g * z.val.1.1.val) * C.base z.val.1.2))
        (z.val.2.val * Matrix.SpecialLinearGroup.transvection s.distinct
          (t - rootParameter s.root.1 s.root.2 k (C.factorBase s g z.val))) := by
  rw [C.factorSlice_param s g k z t]
  change Quotient.mk _ ((g * (z.val.1.1.val * (C.base z.val.1.2 * z.val.2.val))) *
      Matrix.SpecialLinearGroup.transvection s.distinct _) =
    Quotient.mk _ (((g * z.val.1.1.val) * C.base z.val.1.2) *
      (z.val.2.val * Matrix.SpecialLinearGroup.transvection s.distinct _))
  simp only [mul_assoc]

end RootPrefixCoordinates

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ShiftedRootPullback
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

lemma shiftedRootFactorCoordinateMap_embedding {n : ℕ} {a b k : Fin n}
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e)
    (τ : T × B → ℝ) (hτ : Measurable τ) :
    MeasurableEmbedding (shiftedRootFactorCoordinateMap e τ) :=
  (he.prodMap MeasurableEmbedding.id).comp (realFiberShift τ hτ).measurableEmbedding

def shiftedRootFactorPullback {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k) (μ : Measure (X n))
    (e : T × B → RootSlice a b k) (τ : T × B → ℝ) : Measure (T × (B × ℝ)) :=
  ((A.coordinateMeasure μ).comap (shiftedRootFactorCoordinateMap e τ)).map MeasurableEquiv.prodAssoc

lemma shiftedRootFactorPullback_finite {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e)
    (τ : T × B → ℝ) (hτ : Measurable τ) :
    IsFiniteMeasure (shiftedRootFactorPullback hab A μ e τ) := by
  have hf := shiftedRootFactorCoordinateMap_embedding e he τ hτ
  have : IsFiniteMeasure ((A.coordinateMeasure μ).comap (shiftedRootFactorCoordinateMap e τ)) := ⟨by
    rw [hf.comap_apply]
    exact lt_of_le_of_lt (measure_mono (subset_univ _)) (measure_lt_top _ univ)⟩
  unfold shiftedRootFactorPullback
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootCompactTransversals
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root boxes around compact transverse families in one free orbit -/

noncomputable section
open Matrix Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootBox_contains_compact_transverse {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (S : Set (RootSlice a b k)) (hS : IsCompact S)
    (hinj : Set.InjOn (rootQuotientParametrization hab) (S ×ˢ univ))
    (I : Set ℝ) (hI : IsCompact I) :
    ∃ A : RootBox hab k, S ⊆ A.transverse ∧ I ⊆ A.time := by
  obtain ⟨W,hW,hSW,hemb⟩ := compact_injective_localHomeomorph_neighborhood
    (rootQuotientParametrization_localHomeomorph hab) (hS.prod hI)
      (hinj.mono (prod_mono_right (subset_univ I)))
  obtain ⟨U,V,hU,hV,hSU,hIV,hUV⟩ := generalized_tube_lemma hS hI hW hSW
  have he := hemb.comp (Topology.IsOpenEmbedding.inclusion hUV
    ((hU.prod hV).preimage continuous_subtype_val))
  exact ⟨⟨U,V,hU,hV,he⟩,hSU,hIV⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CompactPhysicalRectangles
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical rectangles containing prescribed compact orbit pieces -/

noncomputable section
open Matrix Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_shifted_root_rectangle_covering_compact
    {T B : Type*} [TopologicalSpace T] [TopologicalSpace B]
    {D : Set (T × B)} (hD : IsOpen D)
    {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (e : D → RootSlice a b k) (he : Topology.IsOpenEmbedding e)
    (τ : D → ℝ) (hτ : Continuous τ) (s : T)
    (hsD : {s} ×ˢ (univ : Set B) ⊆ D)
    (hinj : Set.InjOn (fun z : D × ℝ => rootQuotientParametrization hab (e z.1,z.2))
      ({z : D | z.val.1 = s} ×ˢ univ))
    (K : Set B) (hK : IsCompact K) (I : Set ℝ) (hI : IsCompact I) (hne : I.Nonempty)
    (V : Set B) (hV : IsOpen V) (hKV : K ⊆ V)
    (I₀ : Set ℝ) (hI₀ : IsOpen I₀) (hII₀ : I ⊆ I₀) :
    ∃ (Q : RootTransverseRectangle D) (A : RootBox hab k) (R : ℝ) (J : Set ℝ),
      IsOpen J ∧ s ∈ Q.first ∧ K ⊆ Q.second ∧ I ⊆ J ∧
      Q.second ⊆ V ∧ J ⊆ I₀ ∧
      A.transverse = range (e ∘ Q.inclusion) ∧ A.time ⊆ rootLeafWindow R 0 ∧
      ∀ w : Q.first × Q.second, (Homeomorph.addRight (τ (Q.inclusion w))) '' J ⊆ A.time := by
  let f : K → D := fun w => ⟨(s,w.val),hsD ⟨rfl,mem_univ _⟩⟩
  have hf : Continuous f :=
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let P : Set D := range f
  have hP : IsCompact P := isCompact_range hf
  have hS : IsCompact (e '' P) := hP.image he.continuous
  have hi : Set.InjOn (rootQuotientParametrization hab) ((e '' P) ×ˢ univ) := by
    rintro ⟨x,t⟩ ⟨⟨z,⟨w,rfl⟩,rfl⟩,_⟩ ⟨y,u⟩ ⟨⟨z',⟨w',rfl⟩,rfl⟩,_⟩ h
    have H := hinj (x₁ := (f w,t)) (x₂ := (f w',u))
      ⟨rfl,mem_univ _⟩ ⟨rfl,mem_univ _⟩ h
    exact congrArg (fun z : D × ℝ => (e z.1,z.2)) H
  let F : D × ℝ → RootSlice a b k × ℝ := fun z => (e z.1,z.2 + τ z.1)
  have hF : Continuous F := (he.continuous.comp continuous_fst).prodMk
    (continuous_snd.add (hτ.comp continuous_fst))
  have hb : IsCompact ((fun z : D × ℝ => z.2 + τ z.1) '' (P ×ˢ I)) :=
    (hP.prod hI).image (continuous_snd.add (hτ.comp continuous_fst))
  obtain ⟨R,_,hR⟩ := hb.isBounded.exists_pos_norm_lt
  have hRI : ∀ z ∈ P ×ˢ I, z.2 + τ z.1 ∈ Ioo (-R) R := by
    intro z hz
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hR _ ⟨z,hz,rfl⟩)
  obtain ⟨A,hSA,hIA⟩ := rootBox_contains_compact_transverse hab (e '' P) hS hi
    (Icc (-R) R) isCompact_Icc
  let W := A.time ∩ Ioo (-R) R
  have hW : IsOpen W := A.time_open.inter isOpen_Ioo
  have hPW : P ×ˢ I ⊆ F ⁻¹' (A.transverse ×ˢ W) := by
    intro z hz
    exact ⟨hSA ⟨z.1,hz.1,rfl⟩,hIA (Ioo_subset_Icc_self (hRI z hz)),hRI z hz⟩
  obtain ⟨Z,J,hZ,hJ,hPZ,hIJ,hZJ⟩ := generalized_tube_lemma hP hI
    ((A.transverse_open.prod hW).preimage hF) hPW
  have hZO : IsOpen ((Subtype.val '' Z) ∩ (univ ×ˢ V)) :=
    (hD.isOpenEmbedding_subtypeVal.isOpenMap Z hZ).inter (isOpen_univ.prod hV)
  have hsKO : {s} ×ˢ K ⊆ (Subtype.val '' Z) ∩ (univ ×ˢ V) := by
    rintro ⟨u,w⟩ ⟨hu,hw⟩
    have hu' : u=s := hu
    subst u
    exact ⟨⟨f ⟨w,hw⟩,hPZ ⟨⟨w,hw⟩,rfl⟩,rfl⟩,mem_univ _,hKV hw⟩
  obtain ⟨U,V',hU,hV',hsU,hKV',hUV'⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({s} : Set T)) hK hZO hsKO
  let Q : RootTransverseRectangle D := ⟨U,V',hU,hV',by
    intro z hz
    obtain ⟨v,_,hv⟩ := (hUV' hz).1
    exact hv ▸ v.prop⟩
  have hQZ : ∀ w : Q.first × Q.second, Q.inclusion w ∈ Z := by
    intro w
    obtain ⟨v,hv,heq⟩ := (hUV'
      (show (w.1.val,w.2.val) ∈ U ×ˢ V' from ⟨w.1.prop,w.2.prop⟩)).1
    have hv' : v=Q.inclusion w := Subtype.ext heq
    exact hv' ▸ hv
  obtain ⟨t,ht⟩ := hne
  have hsub : range (e ∘ Q.inclusion) ⊆ A.transverse := by
    rintro _ ⟨w,rfl⟩
    exact (hZJ (show (Q.inclusion w,t) ∈ Z ×ˢ J from ⟨hQZ w,hIJ ht⟩)).1
  let A' := A.shrink (range (e ∘ Q.inclusion)) W
    (he.comp (Q.inclusion_isOpenEmbedding hD)).isOpen_range hW hsub inter_subset_left
  refine ⟨Q,A',R,J ∩ I₀,hJ.inter hI₀,hsU rfl,hKV',
    fun _ ht => ⟨hIJ ht,hII₀ ht⟩,?_,inter_subset_right,rfl,?_,?_⟩
  · intro w hw
    exact (hUV' (show (s,w) ∈ U ×ˢ V' from ⟨hsU (Set.mem_singleton s),hw⟩)).2.2
  · intro u hu
    simpa only [rootLeafWindow,Nat.cast_zero,add_zero] using hu.2
  · intro w u hu
    obtain ⟨r,hr,rfl⟩ := hu
    exact (hZJ (show (Q.inclusion w,r) ∈ Z ×ˢ J from ⟨hQZ w,hr.1⟩)).2

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingRootProductBoxes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unconditional local product boxes at every ordered-root step -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace RootPrefixCoordinates
variable {n : ℕ} (q : InitialRootStep n) {T : Type*} [TopologicalSpace T]
  (C : RootPrefixCoordinates n q.processed T) (g : G n) (k : Fin n)

lemma rectangleSlice_orbit (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (s : Q.first) (w : Q.second) (t : ℝ) :
    rootQuotientParametrization q.distinct (C.rectangleSlice q g k Q (s,w),t) =
      rightAction (Quotient.mk _ ((g * s.val.1.val) * C.base s.val.2))
        (w.val.val * Matrix.SpecialLinearGroup.transvection q.distinct
          (t - C.rectangleTime q g k Q (s,w))) :=
  C.factorSlice_orbit q g k (Q.inclusion (s,w)) t

end RootPrefixCoordinates

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FactorPivotCylinder
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The pivot domain contains whole remaining-group fibers -/

noncomputable section
open Matrix Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {n : ℕ} (q : InitialRootStep n) {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates n q.processed T) (g : G n) (k : Fin n)

lemma factorBase_pivot_column (s : UpperRootTransverse n × T)
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) :
    (C.factorBase q g (s,w)).val k q.root.1 =
      ((g * s.1.val) * C.base s.2).val k q.root.1 := by
  let v : positiveRootGeneratedGroup q.remaining :=
    ⟨w.val,positiveRootGeneratedGroup_mono (Finset.erase_subset _ _) w.prop⟩
  have hw : ∀ j, w.val.val j q.root.1 = if j = q.root.1 then 1 else 0 :=
    q.remaining_standard_column v
  change (g * (s.1.val * (C.base s.2 * w.val))).val k q.root.1 = _
  simp only [←mul_assoc]
  change ∑ j, ((g * s.1.val) * C.base s.2).val k j * w.val.val j q.root.1 = _
  simp [hw]

lemma factorPivotDomain_cylinder (s : UpperRootTransverse n × T)
    (hs : ((g * s.1.val) * C.base s.2).val k q.root.1 ≠ 0) :
    {s} ×ˢ (univ : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) ⊆
      C.factorPivotDomain q g k := by
  rintro ⟨u,w⟩ ⟨hu,_⟩
  have hu' : u = s := hu
  subst u
  change (C.factorBase q g (s,w)).val k q.root.1 ≠ 0
  rw [C.factorBase_pivot_column q g k]
  exact hs

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootTranslateBox
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Translation covariance of root boxes

A measure-preserving root translation transports the actual coordinate
measure and its disintegration. This is the local input for identifying
invariant root conditionals with Lebesgue measure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets
open PrimeDegreePackets.RootBox
namespace RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

def translate (B : PrimeDegreePackets.RootBox hij k) (a : ℝ) :
    PrimeDegreePackets.RootBox hij k := by
  let E := timeTranslation (i := i) (j := j) (k := k) a
  let f := Homeomorph.addRight a
  have hiff (z : RootSlice i j k × ℝ) :
      z ∈ B.domain ↔ E z ∈ B.transverse ×ˢ (f '' B.time) := by
    change (z.1 ∈ B.transverse ∧ z.2 ∈ B.time) ↔
      (z.1 ∈ B.transverse ∧ f z.2 ∈ f '' B.time)
    rw [f.injective.mem_set_image]
  let eb := E.subtype hiff
  refine ⟨B.transverse, f '' B.time, B.transverse_open,
    f.isOpenMap _ B.time_open, ?_⟩
  have H := (rightActionHomeomorph (Matrix.SpecialLinearGroup.transvection hij a)).isOpenEmbedding.comp
    (B.embedding.comp eb.symm.isOpenEmbedding)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  have he : E (eb.symm z).val = z.val := congrArg Subtype.val (eb.apply_symm_apply z)
  change rootQuotientParametrization hij z.val =
    rightAction (rootQuotientParametrization hij (eb.symm z).val)
      (Matrix.SpecialLinearGroup.transvection hij a)
  rw [← he]
  exact rootQuotientParametrization_add hij _ _ _

end RootBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FactorSliceFreeness
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A free remaining-group orbit separates the whole root transversal -/

noncomputable section
open Matrix Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {n : ℕ} (q : InitialRootStep n) {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates n q.processed T) (g : G n) (k : Fin n)

theorem factorSlice_fiber_injective_of_free (s : UpperRootTransverse n × T)
    (hfree : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction (Quotient.mk _ ((g*s.1.val)*C.base s.2)) v =
        Quotient.mk _ ((g*s.1.val)*C.base s.2) → v = 1) :
    Set.InjOn (fun z : C.factorPivotDomain q g k × ℝ =>
      rootQuotientParametrization q.distinct (C.factorSlice q g k z.1,z.2))
      ({z : C.factorPivotDomain q g k | z.val.1 = s} ×ˢ univ) := by
  have hi : Function.Injective (fun v : positiveRootGeneratedGroup q.remaining =>
      rightAction (Quotient.mk _ ((g*s.1.val)*C.base s.2)) v.val) := by
    intro v w he
    have h := congrArg (fun x => rightAction x w.val⁻¹) he
    rw [rightAction_mul,rightAction_mul,mul_inv_cancel,rightAction_one] at h
    have h1 := hfree (v.val*w.val⁻¹)
      ((positiveRootGeneratedGroup _).mul_mem
        (positiveRootGeneratedGroup_mono Finset.sdiff_subset v.prop)
        ((positiveRootGeneratedGroup _).inv_mem
          (positiveRootGeneratedGroup_mono Finset.sdiff_subset w.prop))) h
    exact Subtype.ext (mul_inv_eq_one.mp h1)
  rintro ⟨z,t⟩ ⟨hz,_⟩ ⟨w,u⟩ ⟨hw,_⟩ h
  change rootQuotientParametrization q.distinct (C.factorSlice q g k z,t) =
    rootQuotientParametrization q.distinct (C.factorSlice q g k w,u) at h
  change z.val.1 = s at hz
  change w.val.1 = s at hw
  rw [C.factorSlice_orbit q g k,C.factorSlice_orbit q g k] at h
  have he : q.remainingFactor (z.val.2,t-C.factorTime q g k z) =
      q.remainingFactor (w.val.2,u-C.factorTime q g k w) := by
    apply hi
    simpa only [q.remainingFactor_val,hz,hw,factorTime] using h
  have hp := q.remainingFactor.injective he
  have hzw : z=w := Subtype.ext (Prod.ext (hz.trans hw.symm) (congrArg Prod.fst hp))
  subst w
  have ht : t=u := by
    have H := congrArg Prod.snd hp
    exact sub_left_inj.mp H
  exact Prod.ext rfl ht

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootDiagonalCharts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The diagonal action on actual full upper-root quotient boxes -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def upperRootTransverseDiagonal {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) (s : UpperRootTransverse n) : UpperRootTransverse n :=
  ⟨s.val * diagonalOneParameter ell hell t, by
    constructor
    · intro p hp
      rw [mul_diagonalOneParameter_entry, s.prop.1 p hp, zero_mul]
    · intro r hr
      rw [mul_diagonalOneParameter_entry]
      exact mul_ne_zero (s.prop.2 r hr) (Real.exp_ne_zero _)⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralTransverseCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

abbrev PositiveTransverse (n : ℕ) :=
  {s : UpperRootTransverse n // ∀ i, 0 < s.val.val i i}

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralUpperRootChart
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Move the neutral coordinate to the right of the root coordinate

The parametrization is now lower-unitriangular, upper-unipotent, diagonal.
Consequently right translation by the diagonal group is translation in the
last coordinate, with the other two coordinates fixed.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

def neutralUpperRootParam (n : ℕ)
    (z : UnitDiagonalTransverse n × (UpperRootTime n × transverseNeutralSpace n)) : G n :=
  z.1.val.val*(completeRootChain n).word z.2.1*
    diagonalOneParameter z.2.2.val z.2.2.prop 1

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralCoordinateMeasure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Translation invariance in the actual neutral product chart -/

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

def neutralProductParam (n : ℕ)
    (z : NeutralCoordinateBase n × transverseNeutralSpace n) : G n :=
  neutralUpperRootParam n (z.1.1,(z.1.2,z.2))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixLift
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root-prefix box measures agree with the actual covering lift -/

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {T : Type*} [TopologicalSpace T]

def timeGroupParam (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries=allPositiveRoots n) (g : G n)
    (z : (UpperRootTransverse n × T) × c.Time) : G n :=
  g*C.groupParam (z.1.1,(z.1.2,c.remainingWordHomeomorph hP hf z.2))

end RootPrefixCoordinates

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralPrefixMap
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual change from neutral coordinates to full-root prefix coordinates -/

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma emptyRootPattern (n : ℕ) : InitialRootPattern (∅ : Finset (Fin n × Fin n)) := by
  intro p hp
  simp at hp

abbrev neutralEmptyPrefix (n : ℕ) : RootPrefixCoordinates n ∅ PUnit.{1} :=
  RootPrefixCoordinates.empty n

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PhysicalRootRectangles
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical root rectangles represent the actual ambient measure -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]

namespace RootPrefixCoordinates
variable {n : ℕ} (q : InitialRootStep n) {S : Type*} [TopologicalSpace S]
  (C : RootPrefixCoordinates n q.processed S) (g : G n) (k : Fin n)

lemma rectangle_physicalParam (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (z : Q.first × (Q.second × ℝ)) :
    physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q) z =
      rightAction (Quotient.mk _ ((g * z.1.val.1.val) * C.base z.1.val.2))
        (z.2.1.val.val * Matrix.SpecialLinearGroup.transvection q.distinct z.2.2) := by
  change rootQuotientParametrization q.distinct
    (C.rectangleSlice q g k Q (z.1,z.2.1),z.2.2 + C.rectangleTime q g k Q (z.1,z.2.1)) = _
  rw [C.rectangleSlice_orbit q g k Q,add_sub_cancel_right]

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PhysicalRootEmbeddings
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quotient embeddings of physical root rectangles -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]
  [TopologicalSpace T] [TopologicalSpace B]

omit [MeasurableSpace T] [MeasurableSpace B] in
lemma physicalRootCoordinates_isOpenEmbedding {n : ℕ} {a b k : Fin n}
    (e : T × B → RootSlice a b k) (he : Topology.IsOpenEmbedding e)
    (τ : T × B → ℝ) (hτ : Continuous τ) :
    Topology.IsOpenEmbedding (physicalRootCoordinates e τ) := by
  exact (he.prodMap (Topology.IsOpenEmbedding.id (X := ℝ))).comp
    ((fiberShear (Homeomorph.refl (T × B)) τ hτ).isOpenEmbedding.comp
      (Homeomorph.prodAssoc T B ℝ).symm.isOpenEmbedding)

omit [MeasurableSpace T] [MeasurableSpace B] in
theorem physicalRootParam_isOpenEmbedding {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k)
    (e : T × B → RootSlice a b k) (he : Topology.IsOpenEmbedding e)
    (τ : T × B → ℝ) (hτ : Continuous τ)
    (D : Set (T × (B × ℝ))) (hD : IsOpen D)
    (hDA : physicalRootCoordinates e τ '' D ⊆ A.domain) :
    Topology.IsOpenEmbedding (D.domRestrict (physicalRootParam hab e τ)) := by
  let F : D → A.domain := fun z =>
    ⟨physicalRootCoordinates e τ z.val,hDA ⟨z.val,z.prop,rfl⟩⟩
  have hF : Topology.IsOpenEmbedding F := by
    apply Topology.IsOpenEmbedding.of_comp F
      (A.transverse_open.prod A.time_open).isOpenEmbedding_subtypeVal
    exact (physicalRootCoordinates_isOpenEmbedding e he τ hτ).comp hD.isOpenEmbedding_subtypeVal
  exact A.embedding.comp hF

namespace RootPrefixCoordinates
variable {n : ℕ} (q : InitialRootStep n) {S : Type*} [TopologicalSpace S]
  (C : RootPrefixCoordinates n q.processed S) (g : G n) (k : Fin n)

lemma rectangle_coordinates_inside
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k)
    (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time) :
    physicalRootCoordinates (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q) ''
      (univ ×ˢ (univ ×ˢ J)) ⊆ A.domain := by
  rintro _ ⟨z,hz,rfl⟩
  constructor
  · rw [hA]
    exact ⟨(z.1,z.2.1),rfl⟩
  · exact hwindow (z.1,z.2.1) ⟨z.2.2,hz.2.2,rfl⟩

end RootPrefixCoordinates

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PrefixTimeExchange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The root-order exchange as an actual extended-prefix time chart -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T)
    {D : Finset (Fin (d+1))}
    (c : EliminationChain (insert q.root q.processed) D)
    (hfinal : c.finalEntries = allPositiveRoots (d+1))

def nextTimeCoordinates : positiveRootGeneratedGroup (q.remaining.erase q.root) ≃ₜ c.Time :=
  q.nextGroupCast.trans (c.remainingWordHomeomorph q.next_initial hfinal).symm

def prefixTimeExchange :
    ((UpperRootTransverse (d+1) × T) ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) ≃ₜ
    ((UpperRootTransverse (d+1) × (T × ℝ)) × c.Time) :=
  (((Homeomorph.refl (UpperRootTransverse (d+1) × T)).prodCongr
      (q.rootOrderCoordinates d)).trans
    (Homeomorph.prodAssoc (UpperRootTransverse (d+1) × T) ℝ
      (positiveRootGeneratedGroup (q.remaining.erase q.root))).symm).trans
    ((Homeomorph.prodAssoc (UpperRootTransverse (d+1)) T ℝ).prodCongr
      (nextTimeCoordinates q c hfinal))

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootRectangleMeasures
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The included independent rectangles have the actual ambient measure -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

def rectangleBasePoint (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (s : Q.first) : X (d+1) :=
  C.quotientParam g (s.val.1,(s.val.2,1))

lemma rectangle_includedFiberPoint
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (z : Q.first × (Q.second × ℝ)) :
    q.rootFiberPoint d (C.rectangleBasePoint q g k Q)
        (q.includeRootRectangle d Subtype.val z) =
      physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q) z := by
  change rightAction (C.quotientParam g (z.1.val.1,(z.1.val.2,1)))
    (z.2.1.val.val * Matrix.SpecialLinearGroup.transvection q.distinct z.2.2) = _
  rw [C.quotientParam_eq_action]
  change rightAction (rightAction (Quotient.mk _ ((g*z.1.val.1.val)*C.base z.1.val.2)) 1) _ = _
  rw [rightAction_one]
  exact (C.rectangle_physicalParam q g k Q z).symm

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PhysicalPrefixMeasure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent physical rectangles in the full prefix coordinates -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*}
    [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

def unrestrictedPrefixBasePoint (s : UpperRootTransverse (d+1) × T) : X (d+1) :=
  C.quotientParam g (s.1,(s.2,1))

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PhysicalPrefixCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical rectangles in the original remaining-subgroup time chart -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain q.processed D)
    (hf : c.finalEntries = allPositiveRoots (d+1))

def remainingFactorTime :
    (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) ≃ₜ c.Time :=
  q.remainingFactor.trans (c.remainingWordHomeomorph q.initial hf).symm

def physicalPrefixCoordinates {T : Type*} [TopologicalSpace T] :
    ((UpperRootTransverse (d+1) × T) ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) ≃ₜ
      ((UpperRootTransverse (d+1) × T) × c.Time) :=
  (Homeomorph.refl _).prodCongr (remainingFactorTime q c hf)

variable {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

lemma physicalPrefixCoordinates_param
    (z : (UpperRootTransverse (d+1) × T) ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) :
    C.timeParam c q.initial hf g (physicalPrefixCoordinates (T := T) q c hf z) =
      q.rootFiberPoint d (unrestrictedPrefixBasePoint (q := q) (C := C) (g := g)) z := by
  change C.quotientParam g (z.1.1,(z.1.2,
      c.remainingWordHomeomorph q.initial hf
        ((c.remainingWordHomeomorph q.initial hf).symm (q.remainingFactor z.2)))) = _
  erw [Homeomorph.apply_symm_apply,C.quotientParam_eq_action]
  change _ = rightAction (C.quotientParam g (z.1.1,(z.1.2,1))) _
  rw [C.quotientParam_eq_action]
  change _ = rightAction (rightAction (Quotient.mk _ ((g*z.1.1.val)*C.base z.1.2)) 1) _
  rw [rightAction_one]
  rfl

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PrefixRegionFibers
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fibers of an exchanged physical rectangle -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain (insert q.root q.processed) D)
    (hf : c.finalEntries = allPositiveRoots (d+1))

def nextTimeFiber (t : ℝ) :
    positiveRootGeneratedGroup (q.remaining.erase q.root) ≃ₜ c.Time :=
  (q.nextConjugationHomeomorph d t).trans (nextTimeCoordinates q c hf)

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixProductKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual box kernels recovered from the intrinsic root product

The center of a box need not be a generic point.  The formula below uses
the product at the sampled point, translates it back, and normalizes on
the actual time domain of the box.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP : InitialRootPattern P} {c : EliminationChain P D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates (d+1) P T} {g : G (d+1)}

/-- The intrinsic product transported from the sampled point to the
uncentered time coordinates of the box. -/
def uncenteredIntrinsicProduct (_A : RootPrefixBox C c hP hf g)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (z : (UpperRootTransverse (d+1) × T) × c.Time) : Measure c.Time :=
  ((c.remainingIntrinsicProduct hP hf μ (C.timeParam c hP hf g z)).map
    (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hf z.2))).map
      (c.remainingWordHomeomorph hP hf).symm

/-- The normalized intrinsic-product description of a box conditional. -/
def intrinsicProductConditional (A : RootPrefixBox C c hP hf g)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (z : (UpperRootTransverse (d+1) × T) × c.Time) : Measure c.Time :=
  (anchorNormalize (A.uncenteredIntrinsicProduct μ z) A.time).restrict A.time

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralPatchNull
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transfer the neutral graph's full measure to the quotient patch -/

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

abbrev neutralQuotientParam (n : ℕ) (g : G n)
    (z : NeutralCoordinateBase n × transverseNeutralSpace n) : X n :=
  Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g*neutralProductParam n z)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_WeylRootBoxes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

lemma rootReindexCoordinates_param {n : ℕ} (e : Equiv.Perm (Fin n))
    {i j k : Fin n} (hij : i ≠ j) (z : RootSlice i j k × ℝ) :
    rootQuotientParametrization (e.injective.ne hij) (rootReindexCoordinates e i j k z) =
      quotientReindex e (rootQuotientParametrization hij z) := by
  change Quotient.mk _ ((reindexSpecialLinear ℝ e z.1.val) *
    Matrix.SpecialLinearGroup.transvection (e.injective.ne hij) z.2) =
      Quotient.mk _ (reindexSpecialLinear ℝ e
        (z.1.val * Matrix.SpecialLinearGroup.transvection hij z.2))
  rw [map_mul, reindex_transvection]

namespace RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

def reindex (B : PrimeDegreePackets.RootBox hij k) (e : Equiv.Perm (Fin n)) :
    PrimeDegreePackets.RootBox (e.injective.ne hij) (e k) := by
  let S := rootSliceReindexHomeomorph e i j k
  let E := rootReindexCoordinates e i j k
  have hiff (z : RootSlice i j k × ℝ) :
      z ∈ B.domain ↔ E z ∈ (S '' B.transverse) ×ˢ B.time := by
    change (z.1 ∈ B.transverse ∧ z.2 ∈ B.time) ↔
      (S z.1 ∈ S '' B.transverse ∧ z.2 ∈ B.time)
    rw [S.injective.mem_set_image]
  let eb := E.subtype hiff
  refine ⟨S '' B.transverse, B.time, S.isOpenMap _ B.transverse_open,
    B.time_open, ?_⟩
  have H := (quotientReindexHomeomorph e).isOpenEmbedding.comp
    (B.embedding.comp eb.symm.isOpenEmbedding)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  have he : E (eb.symm z).val = z.val := congrArg Subtype.val (eb.apply_symm_apply z)
  change rootQuotientParametrization (e.injective.ne hij) z.val =
    quotientReindex e (rootQuotientParametrization hij (eb.symm z).val)
  rw [← he]
  exact rootReindexCoordinates_param e hij _

end RootBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayDescent
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

variable [NeZero N]



def classValue (c : ClassGroup (𝓞 K)) : ℂˣ :=
  ψ.idealHom (integralIdealFractionalUnit (classIdeal K N c).val (classIdeal_ne_bot c))

end EvenRayCharacter

end PrimeDegreePackets

end

end OAI
end


