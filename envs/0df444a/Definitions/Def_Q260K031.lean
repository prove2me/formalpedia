-- Prove2me | Definitions.Def_Q260K031
-- name    : Q260K031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T07:28:09.6891+00:00
-- url     : https://prove2.me/theorems/21d93d2f-802e-49c7-ac86-bae1fc0f9c38
-- title:
--   Definitions bundle Q260K031 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 38 declarations of OpenAI's Lean: 15 definitions, 1 instance and 22 theorems. The definitions and types are `OAI.KadisonKastler.ScalarBoundaryMean.restrictedOperatorMean`, `OAI.KadisonKastler.algebraConstantField`, `OAI.KadisonKastler.constantAlgebraUnitaryFamily`, `OAI.KadisonKastler.faithfulCyclicAlgebra`, `OAI.KadisonKastler.faithfulCyclicVector`, `OAI.KadisonKastler.graphDiagonalUnitary`, `OAI.KadisonKastler.graphFlipValue`, `OAI.KadisonKastler.graphReciprocalFlip`, `OAI.KadisonKastler.graphResolvent`, `OAI.KadisonKastler.rescaledGraphOperatorMap`, `OAI.KadisonKastler.rescaledGraphProjection`, `OAI.KadisonKastler.rescaledGraphSignalMap`, `OAI.KadisonKastler.rescaledGraphSubspace`, `OAI.KadisonKastler.tomitaGraphFirst`, `OAI.KadisonKastler.tomitaGraphFlip`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`KadisonKastler_ConstantFieldCocycle`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ConstantFieldCocycle.lean), [`KadisonKastler_FaithfulCyclicConstruction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/FaithfulCyclicConstruction.lean), [`KadisonKastler_GraphOrbitSelection`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/GraphOrbitSelection.lean), [`KadisonKastler_GraphReciprocal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/GraphReciprocal.lean), [`KadisonKastler_GraphResolventCompression`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/GraphResolventCompression.lean), [`KadisonKastler_RescaledGraphAction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/RescaledGraphAction.lean), [`KadisonKastler_RescaledTomitaGraph`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/RescaledTomitaGraph.lean), [`KadisonKastler_RestrictedOperatorMean`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/RestrictedOperatorMean.lean), [`KadisonKastler_TomitaGraphInvolution`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/TomitaGraphInvolution.lean), [`KadisonKastler_TomitaPolarCoordinates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/TomitaPolarCoordinates.lean), [`KadisonKastler_TomitaResolventFaithful`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/TomitaResolventFaithful.lean).
--
--   **Imports.** It imports the bundle `Q260K029` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K035` and `Q260K071`; the statements `OAI.KadisonKastler.constantAlgebraUnitaryFamily_defect_le`, `OAI.KadisonKastler.exists_faithfulCyclic_standardTracialPosition`, `OAI.KadisonKastler.exists_initial_cyclic_commutant_neighbor`, `OAI.KadisonKastler.norm_preparedRight_graphProjection_sub_le_of_row_approx` and `OAI.KadisonKastler.statePreservingUnitary_resolvent`; the proofs of `OAI.KadisonKastler.ScalarBoundaryMean.operatorFieldFamilyInclusion_translate`, `OAI_KadisonKastler_centralPairDecomposition_of_rankModel`, `OAI_KadisonKastler_commuting_kms_actions_eq`, `OAI.KadisonKastler.constantAlgebraUnitaryFamily_defect_le` and `OAI.KadisonKastler.operatorFieldConst_representative_ae`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K029

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RestrictedOperatorMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.NonsingularAction.leftOnProduct_apply _root_.OAI.KadisonKastler.WeakOperatorRepresentative.evalHom_apply _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_kernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_positiveKernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.topElement_val _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.randomWalkPathAction_apply _root_.OAI.KadisonKastler.shiftBoundaryAction_apply _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Equivariant averaging within a von Neumann algebra

The constant-commutant description of the field algebra is invariant under
boundary pullback. Restricting the constructed mean therefore keeps both
the cocycle and its correction in the prescribed von Neumann algebra.
-/

namespace KadisonKastler

open MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H)

namespace ScalarBoundaryMean

variable {M} {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
  (hTom : PublishedFieldTomiyama (G := G) (H := H) (μ := μ))

@[simp]
theorem restrictedOperatorMeanValue_coe (M : VonNeumannAlgebra H)
    (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    (m.restrictedOperatorMeanValue hTom M F : WeakOperatorField (H := H) μ) =
      m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F) := rfl

theorem restrictedOperatorMeanValue_add (M : VonNeumannAlgebra H)
    (F K : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    m.restrictedOperatorMeanValue hTom M (F + K) =
      m.restrictedOperatorMeanValue hTom M F + m.restrictedOperatorMeanValue hTom M K := by
  apply Subtype.ext
  change m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (F + K)) =
    m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F) +
      m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M K)
  calc
    _ = m.operatorMean (H := H)
        (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F +
          operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M K) :=
      congrArg (m.operatorMean (H := H))
        ((operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M).map_add F K)
    _ = _ := (m.operatorMean (H := H)).map_add _ _

theorem restrictedOperatorMeanValue_smul (M : VonNeumannAlgebra H)
    (c : ℂ) (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    m.restrictedOperatorMeanValue hTom M (c • F) =
      c • m.restrictedOperatorMeanValue hTom M F := by
  apply Subtype.ext
  change m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (c • F)) =
    c • m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F)
  calc
    _ = m.operatorMean (H := H) (c • operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F) :=
      congrArg (m.operatorMean (H := H))
        (map_smul (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M) c F)
    _ = _ := map_smul (m.operatorMean (H := H)) c _

theorem norm_restrictedOperatorMeanValue_le (M : VonNeumannAlgebra H)
    (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    ‖m.restrictedOperatorMeanValue hTom M F‖ ≤ ‖F‖ :=
  (m.norm_operatorMeanValue_le (H := H) _).trans
    (norm_operatorFieldFamilyInclusion_le (G := G) M F)

/-- Restrict the scalar-coefficient operator mean to M-valued fields. -/
def restrictedOperatorMean (M : VonNeumannAlgebra H) :
    (G →ᵇ operatorFieldAlgebra (μ := μ) M) →L[ℂ] operatorFieldAlgebra (μ := μ) M :=
  LinearMap.mkContinuous
    { toFun := m.restrictedOperatorMeanValue hTom M
      map_add' := m.restrictedOperatorMeanValue_add hTom M
      map_smul' := m.restrictedOperatorMeanValue_smul hTom M }
    1 (fun F => by
      change ‖m.restrictedOperatorMeanValue hTom M F‖ ≤ 1 * ‖F‖
      exact (m.norm_restrictedOperatorMeanValue_le hTom M F).trans_eq (one_mul ‖F‖).symm)

@[simp]
theorem restrictedOperatorMean_coe (M : VonNeumannAlgebra H)
    (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    (m.restrictedOperatorMean hTom M F : WeakOperatorField (H := H) μ) =
      m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F) := rfl

end ScalarBoundaryMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstantFieldCocycle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.WeakOperatorRepresentative.evalHom_apply _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_kernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_positiveKernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.topElement_val _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Correcting a nearby unitary family into an algebra-valued cocycle -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {N : VonNeumannAlgebra H}

/-- Constant fields with values in the specified von Neumann algebra. -/
def algebraConstantField (N : VonNeumannAlgebra H) :
    Algebra N →⋆ₐ[ℂ] operatorFieldAlgebra (μ := μ) N :=
  ((operatorFieldConst μ).comp N.toStarSubalgebra.subtype).codRestrict
    (operatorFieldAlgebra (μ := μ) N) (fun x => by
      apply (mem_operatorFieldAlgebra_iff N _).mpr
      intro T hT
      change operatorFieldConst μ T * operatorFieldConst μ x =
        operatorFieldConst μ x * operatorFieldConst μ T
      rw [← map_mul, ← map_mul]
      exact congrArg (operatorFieldConst μ)
        (((VonNeumannAlgebra.mem_commutant_iff.mp hT) x x.property).symm))

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
@[simp]
theorem algebraConstantField_coe (x : Algebra N) :
    (algebraConstantField (μ := μ) N x : WeakOperatorField (H := H) μ) =
      operatorFieldConst μ x := rfl

/-- A family of algebra unitaries determines a family of constant unitary fields. -/
def constantAlgebraUnitaryFamily (V : G → unitary (Algebra N)) :
    unitary (G →ᵇ operatorFieldAlgebra (μ := μ) N) :=
  boundedUnitaryFamily (fun g => Unitary.map
    (StarMonoidHom.ofClass (algebraConstantField (μ := μ) N)) (V g))

omit [Group G] [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
@[simp]
theorem constantAlgebraUnitaryFamily_coe (V : G → unitary (Algebra N)) (g : G) :
    ((constantAlgebraUnitaryFamily (μ := μ) V).val g : WeakOperatorField (H := H) μ) =
      operatorFieldConst μ (V g) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FaithfulCyclicConstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.countableOperatorEntry_apply _root_.OAI.KadisonKastler.countableOperatorEntry_diagonal_mul _root_.OAI.KadisonKastler.countableOperatorEntry_mul_diagonal _root_.OAI.KadisonKastler.countableTensorAlgebraic_tmul _root_.OAI.KadisonKastler.countableTensorEquiv_symm_single _root_.OAI.KadisonKastler.countableTensorEquiv_tmul _root_.OAI.KadisonKastler.countableTensorIsometry_tmul _root_.OAI.KadisonKastler.countableTensorVector_apply _root_.OAI.KadisonKastler.countableTensorVector_single _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A faithful cyclic representation from a countable amplification

The weighted dense vector is separating for the diagonal action. Its
closed orbit gives a faithful cyclic restriction. Kaplansky density and
weak compactness of the original operator ball show that the restricted
image is already a von Neumann algebra.
-/

namespace KadisonKastler

open Generator Generator.Tracial Filter TopologicalSpace
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] [SeparableSpace H]

def faithfulCyclicVector (M : VonNeumannAlgebra H) : faithfulCyclicSpace M :=
  ⟨denseSeparatingUnitVector, mem_vectorOrbitClosure _ _⟩

omit [Nontrivial H] in
@[simp] theorem faithfulCyclicHom_apply (M : VonNeumannAlgebra H) (a : Algebra M)
    (x : faithfulCyclicSpace M) :
    (faithfulCyclicHom M a x : CountableHilbertSum H) = l2Diagonal a.val x :=
  reducingRestriction_coe_apply _ _
    (fun a _ hy => vectorOrbitClosure_invariant _ _ a hy)
    ((countableDiagonalHom M).rangeRestrict a) x

theorem faithfulCyclicHom_separating (M : VonNeumannAlgebra H) :
    Function.Injective (fun a : Algebra M => faithfulCyclicHom M a (faithfulCyclicVector M)) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply denseSeparatingUnitVector_separating
  have he := congrArg (fun x : faithfulCyclicSpace M => (x : CountableHilbertSum H)) hab
  simp only [faithfulCyclicHom_apply] at he
  change l2Diagonal (a.val - b.val) (denseSeparatingUnitVector (H := H)) = 0
  change (l2DiagonalHom (E := H) (a.val - b.val)) _ = 0
  rw [map_sub]
  exact sub_eq_zero.mpr he

theorem faithfulCyclicHom_injective (M : VonNeumannAlgebra H) :
    Function.Injective (faithfulCyclicHom M) := by
  intro a b hab
  exact faithfulCyclicHom_separating M (congrArg (fun T => T (faithfulCyclicVector M)) hab)

theorem faithfulCyclicHom_norm (M : VonNeumannAlgebra H) (a : Algebra M) :
    ‖faithfulCyclicHom M a‖ = ‖a‖ := by
  let : CStarAlgebra (Algebra M) := {}
  let : CStarAlgebra (faithfulCyclicSpace M →L[ℂ] faithfulCyclicSpace M) := {}
  exact NonUnitalStarAlgHom.norm_map (faithfulCyclicHom M) (faithfulCyclicHom_injective M) a

omit [Nontrivial H] in
theorem faithfulCyclicHom_tendsto_weak (M : VonNeumannAlgebra H)
    {ι : Type*} {l : Filter ι} (a : ι → Algebra M) (b : Algebra M) (C : ℝ)
    (hn : ∀ᶠ i in l, ‖a i‖ ≤ C)
    (hweak : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (b.val x)))) (x y : faithfulCyclicSpace M) :
    Tendsto (fun i => inner ℂ y (faithfulCyclicHom M (a i) x)) l
      (𝓝 (inner ℂ y (faithfulCyclicHom M b x))) := by
  simpa only [Submodule.coe_inner, faithfulCyclicHom_apply] using
    l2Diagonal_tendsto_weak (fun i => (a i).val) b.val C hn hweak x.val y.val

def faithfulCyclicAlgebra (M : VonNeumannAlgebra H) :
    VonNeumannAlgebra (faithfulCyclicSpace M) :=
  generatedVonNeumannAlgebra (faithfulCyclicHom M).range

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RescaledTomitaGraph
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Rescaled Tomita graphs in a fixed two-coordinate Hilbert space

A fixed conjugation identifies the conjugate copy of the Hilbert space
with the original one. In these coordinates the graph vector is
`(x Ω, c J (x* Ω))`. The same identification is used for both algebras.
No closability or modular spectral theorem is needed for the closed
linear graph subspace or the elementary projection comparison below.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The closed linear rescaled graph. -/
def rescaledGraphSubspace (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) : Submodule ℂ (TomitaGraphHilbert H) :=
  (rescaledGraphMap P J Ω c).range.topologicalClosure

instance rescaledGraphSubspace_complete (P : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) :
    CompleteSpace (rescaledGraphSubspace P J Ω c) :=
  inferInstanceAs (CompleteSpace (rescaledGraphMap P J Ω c).range.topologicalClosure)

/-- Orthogonal projection onto the closed graph. -/
def rescaledGraphProjection (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H :=
  (rescaledGraphSubspace P J Ω c).starProjection

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RescaledGraphAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The common unitary action on rescaled graphs

Left and right multiplication by common unitaries acts on graph vectors
through one unitary of the fixed two-coordinate Hilbert space. Thus each
closed graph reduces this unitary whenever the right action belongs to
the relevant commutant and has the prescribed value on the common vector.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Two unitary coordinate actions form an actual Hilbert-space unitary. -/
def graphDiagonalUnitary (u v : unitary (H →L[ℂ] H)) :
    unitary (TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) :=
  Unitary.linearIsometryEquiv.symm (LinearIsometryEquiv.piLpCongrRight 2
    (fun i : Fin 2 => Unitary.linearIsometryEquiv (if i = 0 then u else v)))

@[simp] theorem graphDiagonalUnitary_apply_zero
    (u v : unitary (H →L[ℂ] H)) (ξ : TomitaGraphHilbert H) :
    (graphDiagonalUnitary u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) ξ 0 =
      (u : H →L[ℂ] H) (ξ 0) := by
  change (Unitary.linearIsometryEquiv (if (0 : Fin 2) = 0 then u else v)) (ξ 0) = _
  rw [ite_eq_left rfl]
  rfl

@[simp] theorem graphDiagonalUnitary_apply_one
    (u v : unitary (H →L[ℂ] H)) (ξ : TomitaGraphHilbert H) :
    (graphDiagonalUnitary u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) ξ 1 =
      (v : H →L[ℂ] H) (ξ 1) := by
  change (Unitary.linearIsometryEquiv (if (1 : Fin 2) = 0 then u else v)) (ξ 1) = _
  rw [ite_eq_right (by decide)]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphOrbitSelection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Actual orbit samples retaining the rescaled graph signal

The finite matrix moment estimate and the Hilbert sign selection are
combined here. The signal is the image of the graph vector under the
specified bounded operator; its invariance is derived from the common
unitary graph action.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The graph formula is linear on all ambient operators. -/
def rescaledGraphOperatorMap (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) :
    (H →L[ℂ] H) →ₗ[ℂ] TomitaGraphHilbert H where
  toFun x := rescaledGraphVector J Ω c x
  map_add' x y := by
    ext i
    fin_cases i <;> simp [rescaledGraphVector, star_add, map_add, smul_add]
  map_smul' z x := by
    ext i
    fin_cases i
    · simp [rescaledGraphVector]
    · change c • J (star (z • x) Ω) = z • (c • J (star x Ω))
      rw [star_smul, smul_apply, J.map_smulₛₗ]
      change c • (star (star z) • J (star x Ω)) = z • (c • J (star x Ω))
      rw [star_star, smul_comm]

/-- The actual graph signal, viewed as a real-linear map for sign sums. -/
def rescaledGraphSignalMap (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) :
    (H →L[ℂ] H) →ₗ[ℝ] TomitaGraphHilbert H :=
  (T.toLinearMap.comp (rescaledGraphOperatorMap J Ω c)).restrictScalars ℝ

@[simp] theorem rescaledGraphSignalMap_apply
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (x : H →L[ℂ] H) :
    rescaledGraphSignalMap J Ω c T x = T (rescaledGraphVector J Ω c x) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphReciprocal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reciprocal rescaling of closed Tomita graphs

Conjugating and interchanging the two coordinates sends the graph at c
to the graph at 1/c. This norm-preserving real-linear map transfers the
directional estimates to small positive scales.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def graphFlipValue (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : TomitaGraphHilbert H) :
    TomitaGraphHilbert H := WithLp.toLp 2 ![J (ξ 1), J (ξ 0)]

omit [CompleteSpace H] in
theorem graphFlipValue_norm (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : TomitaGraphHilbert H) :
    ‖graphFlipValue J ξ‖ = ‖ξ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, graphFlipValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, J.norm_map]
  ring

/-- The reciprocal graph symmetry, viewed as a real-linear isometry. -/
def graphReciprocalFlip (J : H ≃ₗᵢ⋆[ℂ] H) :
    TomitaGraphHilbert H →L[ℝ] TomitaGraphHilbert H :=
  LinearMap.mkContinuous
    { toFun := graphFlipValue J
      map_add' := by
        intro ξ η
        ext i
        fin_cases i <;> simp [graphFlipValue, map_add]
      map_smul' := by
        intro r ξ
        ext i
        fin_cases i <;> simp [graphFlipValue, conjugation_real_smul] }
    1 (fun ξ => by
      change ‖graphFlipValue J ξ‖ ≤ 1 * ‖ξ‖
      rw [one_mul, graphFlipValue_norm])

omit [CompleteSpace H] in
@[simp] theorem graphReciprocalFlip_norm (J : H ≃ₗᵢ⋆[ℂ] H)
    (ξ : TomitaGraphHilbert H) : ‖graphReciprocalFlip J ξ‖ = ‖ξ‖ :=
  graphFlipValue_norm J ξ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphResolventCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Contractive compression of the actual graph projection

The first diagonal entry is the bounded graph resolvent. Its comparison
follows directly from the norm comparison of the whole graph projections.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def graphResolvent (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) : H →L[ℂ] H :=
  Generator.operatorEntry (rescaledGraphProjection P J Ω c) 0 0

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaGraphInvolution
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The involution on the closed Tomita graph

Taking adjoints on the algebraic core becomes a continuous conjugate-linear
coordinate swap. Hence its involution identity survives graph closure.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
/-- Adjoint on graph vectors, with the fixed second-coordinate identification. -/
def tomitaGraphFlip (J : H ≃ₗᵢ⋆[ℂ] H) : TomitaGraphHilbert H ≃ₗᵢ⋆[ℂ] TomitaGraphHilbert H where
  toFun ξ := WithLp.toLp 2 ![J.symm (ξ 1), J (ξ 0)]
  invFun ξ := WithLp.toLp 2 ![J.symm (ξ 1), J (ξ 0)]
  left_inv ξ := by ext i; fin_cases i <;> simp
  right_inv ξ := by ext i; fin_cases i <;> simp
  map_add' ξ η := by ext i; fin_cases i <;> simp [map_add]
  map_smul' z ξ := by ext i; fin_cases i <;> simp [map_smulₛₗ]
  norm_map' ξ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_two]
    change ‖J.symm (ξ 1)‖ ^ 2 + ‖J (ξ 0)‖ ^ 2 = ‖ξ 0‖ ^ 2 + ‖ξ 1‖ ^ 2
    rw [J.symm.norm_map, J.norm_map]
    exact add_comm _ _

omit [CompleteSpace H] in
@[simp] theorem tomitaGraphFlip_zero (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : TomitaGraphHilbert H) :
    tomitaGraphFlip J ξ 0 = J.symm (ξ 1) := rfl

omit [CompleteSpace H] in
@[simp] theorem tomitaGraphFlip_one (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : TomitaGraphHilbert H) :
    tomitaGraphFlip J ξ 1 = J (ξ 0) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaResolventFaithful
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.finiteDiagonalMap_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Faithfulness of the bounded Tomita graph resolvent

Both endpoints of the positive contraction have zero eigenspace. This is the
bounded starting point for recovering the modular operator by spectral calculus.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
theorem inner_tupleSingle_left (i : Fin 2) (x : H) (v : TomitaGraphHilbert H) :
    inner ℂ (Generator.tupleSingle i x) v = inner ℂ x (v i) := by
  fin_cases i <;> simp [PiLp.inner_apply, Fin.sum_univ_two, Generator.tupleSingle_apply,
    Pi.single_apply]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaPolarCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.finiteDiagonalMap_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Polar coordinates for the closed Tomita graph

The first-coordinate map has dense range and zero kernel. Extending the
isometry between the ranges of its adjoint and the positive graph root
identifies the graph Hilbert space with the original Hilbert space.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- First coordinate on the graph Hilbert space. -/
def tomitaGraphFirst (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    rescaledGraphSubspace M J Ω 1 →L[ℂ] H :=
  (Generator.tupleSingle (H := H) (0 : Fin 2)).adjoint.comp
    (rescaledGraphSubspace M J Ω 1).subtypeL

@[simp] theorem tomitaGraphFirst_apply (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (ξ : rescaledGraphSubspace M J Ω 1) : tomitaGraphFirst (M := M) J Ω ξ = ξ.val 0 := by
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x ((Generator.tupleSingle (H := H) (0 : Fin 2)).adjoint ξ.val) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [PiLp.inner_apply, Fin.sum_univ_two, Generator.tupleSingle_apply, Pi.single_apply]

@[simp] theorem tomitaGraphFirst_adjoint_apply (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (x : H) :
    ((tomitaGraphFirst (M := M) J Ω).adjoint x).val =
      rescaledGraphProjection M J Ω 1 (Generator.tupleSingle 0 x) := by
  simp only [tomitaGraphFirst, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_subtypeL, ContinuousLinearMap.adjoint_adjoint]
  rfl

end

end KadisonKastler

end OAI
end


