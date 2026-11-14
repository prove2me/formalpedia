-- Prove2me | Definitions.Def_Q260K045
-- name    : Q260K045
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T20:52:58.618641+00:00
-- url     : https://prove2.me/theorems/993d9469-b7fb-4477-a7d3-c485e2fb2b25
-- title:
--   Definitions bundle Q260K045 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 5 definitions and 8 theorems. The definitions and types are `OAI.KadisonKastler.cyclicLeftRootVector`, `OAI.KadisonKastler.cyclicRightRootVector`, `OAI.KadisonKastler.faithfulTensorEquiv`, `OAI.KadisonKastler.normalTwoStateEquiv`, `OAI.KadisonKastler.normalTwoStateProjection`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`KadisonKastler_CyclicSqrtGaugeBalance`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/CyclicSqrtGaugeBalance.lean), [`KadisonKastler_FaithfulCyclicTensor`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/FaithfulCyclicTensor.lean), [`KadisonKastler_FaithfulTensorRange`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/FaithfulTensorRange.lean), [`KadisonKastler_NormalTwoStateAlgebra`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/NormalTwoStateAlgebra.lean), [`KadisonKastler_NormalTwoStateState`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/NormalTwoStateState.lean), [`KadisonKastler_TracialModularResolution`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/TracialModularResolution.lean).
--
--   **Imports.** It imports the bundles `Q260K074`, `Q260K092`, `Q260K042` and `Q260K044` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K046`; the statements `OAI.KadisonKastler.cyclicRootScalarBalance` and `OAI_KadisonKastler_cyclicSqrtGaugeBalance`; the proofs of `OAI.KadisonKastler.PointedMatrixSites.exists_represented_scalar_bicentralizer`, `OAI.KadisonKastler.PointedMatrixSites.represented_state_homogeneity`, `OAI.KadisonKastler.TwoRatioProductModel.tensor_typeIII1_general`, `OAI_KadisonKastler_TypeIIIFactor_exists_relative_matrix_stage_near_projection`, `OAI_KadisonKastler_commutant_cyclic_of_separating_reference`, `OAI.KadisonKastler.cyclicRootScalarBalance` and `OAI_KadisonKastler_minimal_row_family_right_module`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
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
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
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
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K074
import Definitions.Def_Q260K092
import Definitions.Def_Q260K042
import Definitions.Def_Q260K044

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicSqrtGaugeBalance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two square-root spectral weights in a cyclic gauge model -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H)

def cyclicLeftRootVector : ModularCyclicSpace M J Ω x :=
  ContinuousMap.toLp 2 (modularCyclicMeasure (M := M) J Ω x) ℂ
    (resolventSqrtFunction (graphResolvent M J Ω 1))

def cyclicRightRootVector : ModularCyclicSpace M J Ω x :=
  ContinuousMap.toLp 2 (modularCyclicMeasure (M := M) J Ω x) ℂ
    (resolventComplementSqrtFunction (graphResolvent M J Ω 1))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FaithfulCyclicTensor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.rescaledGraphSubspace_complete _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Tensoring the constructed faithful cyclic representation

The tensor representation is a restriction of countable amplification.
Its defining isometry and its bounded weak continuity are concrete.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator Generator.Tracial Filter
open scoped TensorProduct Topology

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [Nontrivial H] in
theorem faithfulTensorHom_left (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (a : Algebra M) :
    faithfulTensorHom M D ⟨spatialLeft a.val, spatialLeft_mem_product M D a.property⟩ =
      spatialLeft (K := K) (faithfulCyclicHom M a) := by
  apply spatialLinearMap_ext
  intro x y
  apply (faithfulTensorEmbedding M).injective
  refine (faithfulTensorHom_intertwines M D _ _).trans ?_
  rw [faithfulTensorEmbedding_tmul]
  have hl : l2Diagonal (spatialLeft (K := K) a.val) (countableTensorVector x.val y) =
      countableTensorVector (l2Diagonal a.val x.val) y := by
    ext n
    exact (spatialTensorOp_coe a.val (1 : K →L[ℂ] K) (x.val n ⊗ₜ[ℂ] y)).trans
      (by simp only [TensorProduct.mapL_tmul, one_apply_eq_self]; rfl)
  have hr : spatialLeft (K := K) (faithfulCyclicHom M a)
      ((x ⊗ₜ[ℂ] y : faithfulCyclicSpace M ⊗[ℂ] K) :
        SpatialHilbert (faithfulCyclicSpace M) K) =
      (((faithfulCyclicHom M a x) ⊗ₜ[ℂ] y : faithfulCyclicSpace M ⊗[ℂ] K) :
        SpatialHilbert (faithfulCyclicSpace M) K) := by
    exact (spatialTensorOp_coe (faithfulCyclicHom M a) (1 : K →L[ℂ] K)
      (x ⊗ₜ[ℂ] y)).trans (by simp only [TensorProduct.mapL_tmul, one_apply_eq_self])
  exact hl.trans ((congrArg (fun z => countableTensorVector z y)
    (faithfulCyclicHom_apply M a x).symm).trans
      ((faithfulTensorEmbedding_tmul M (faithfulCyclicHom M a x) y).symm.trans
        (congrArg (faithfulTensorEmbedding (K := K) M) hr.symm)))

omit [Nontrivial H] in
theorem faithfulTensorHom_right (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (b : Algebra D) :
    faithfulTensorHom M D ⟨spatialRight b.val, spatialRight_mem_product M D b.property⟩ =
      spatialRight (H := faithfulCyclicSpace M) b.val := by
  apply spatialLinearMap_ext
  intro x y
  apply (faithfulTensorEmbedding M).injective
  refine (faithfulTensorHom_intertwines M D _ _).trans ?_
  rw [faithfulTensorEmbedding_tmul]
  have hl : l2Diagonal (spatialRight (H := H) b.val) (countableTensorVector x.val y) =
      countableTensorVector x.val (b.val y) := by
    ext n
    exact (spatialTensorOp_coe (1 : H →L[ℂ] H) b.val (x.val n ⊗ₜ[ℂ] y)).trans
      (by simp only [TensorProduct.mapL_tmul, one_apply_eq_self]; rfl)
  have hr : spatialRight (H := faithfulCyclicSpace M) b.val
      ((x ⊗ₜ[ℂ] y : faithfulCyclicSpace M ⊗[ℂ] K) :
        SpatialHilbert (faithfulCyclicSpace M) K) =
      ((x ⊗ₜ[ℂ] b.val y : faithfulCyclicSpace M ⊗[ℂ] K) :
        SpatialHilbert (faithfulCyclicSpace M) K) := by
    exact (spatialTensorOp_coe (1 : faithfulCyclicSpace M →L[ℂ] faithfulCyclicSpace M)
      b.val (x ⊗ₜ[ℂ] y)).trans (by simp only [TensorProduct.mapL_tmul, one_apply_eq_self])
  exact hl.trans ((faithfulTensorEmbedding_tmul M x (b.val y)).symm.trans
    (congrArg (faithfulTensorEmbedding (K := K) M) hr.symm))

omit [Nontrivial H] in
theorem faithfulTensorHom_tendsto_weak (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    {ι : Type*} {l : Filter ι} (a : ι → Algebra (spatialProductAlgebra M D))
    (b : Algebra (spatialProductAlgebra M D)) (C : ℝ) (hn : ∀ᶠ i in l, ‖a i‖ ≤ C)
    (hweak : ∀ x y : SpatialHilbert H K,
      Tendsto (fun i => inner ℂ y ((a i).val x)) l (𝓝 (inner ℂ y (b.val x))))
    (x y : SpatialHilbert (faithfulCyclicSpace M) K) :
    Tendsto (fun i => inner ℂ y (faithfulTensorHom M D (a i) x)) l
      (𝓝 (inner ℂ y (faithfulTensorHom M D b x))) := by
  change Tendsto (fun i => inner ℂ y
    ((faithfulTensorEmbedding M).toContinuousLinearMap.adjoint
      (l2Diagonal (a i).val (faithfulTensorEmbedding M x)))) l
    (𝓝 (inner ℂ y ((faithfulTensorEmbedding M).toContinuousLinearMap.adjoint
      (l2Diagonal b.val (faithfulTensorEmbedding M x)))))
  simp only [ContinuousLinearMap.adjoint_inner_right]
  exact l2Diagonal_tendsto_weak (fun i => (a i).val) b.val C hn hweak _ _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FaithfulTensorRange
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.rescaledGraphSubspace_complete _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The tensor isomorphism for the explicit faithful cyclic representation

Only this representation change is needed by fixed-factor preparation.
The range is identified with the spatial product by its two generating
legs and bounded weak continuity, without an arbitrary-isomorphism input.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [Nontrivial H] in
theorem faithfulTensorHom_boundedWeakNormal (M : VonNeumannAlgebra H)
    (D : VonNeumannAlgebra K) :
    BoundedWeakNormal (spatialProductAlgebra M D) (faithfulTensorHom M D) := by
  intro ι l a b C hn hw x y
  exact faithfulTensorHom_tendsto_weak M D a b C hn hw x y

omit [Nontrivial H] in
theorem faithfulTensorHom_generators_map_le
    (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) :
    (M.toStarSubalgebra.map (spatialLeft (H := H) (K := K))) ⊔
      (D.toStarSubalgebra.map (spatialRight (H := H) (K := K))) ≤
    ((spatialProductAlgebra (faithfulCyclicAlgebra M) D).toStarSubalgebra.comap
      (faithfulTensorHom M D)).map (spatialProductAlgebra M D).toStarSubalgebra.subtype := by
  let P := spatialProductAlgebra M D
  let N := spatialProductAlgebra (faithfulCyclicAlgebra M) D
  let B : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    (M.toStarSubalgebra.map (spatialLeft (H := H) (K := K))) ⊔
    (D.toStarSubalgebra.map (spatialRight (H := H) (K := K)))
  let S := N.toStarSubalgebra.comap (faithfulTensorHom M D)
  change B ≤ S.map P.toStarSubalgebra.subtype
  apply sup_le
  · rintro _ ⟨m, hm, rfl⟩
    refine ⟨⟨spatialLeft m, spatialLeft_mem_product M D hm⟩, ?_, rfl⟩
    change faithfulTensorHom M D _ ∈ N
    rw [faithfulTensorHom_left M D ⟨m, hm⟩]
    exact spatialLeft_mem_product (faithfulCyclicAlgebra M) D
      (subset_generatedVonNeumannAlgebra _ ⟨⟨m, hm⟩, rfl⟩)
  · rintro _ ⟨d, hd, rfl⟩
    refine ⟨⟨spatialRight d, spatialRight_mem_product M D hd⟩, ?_, rfl⟩
    change faithfulTensorHom M D _ ∈ N
    rw [faithfulTensorHom_right M D ⟨d, hd⟩]
    exact spatialRight_mem_product (faithfulCyclicAlgebra M) D hd

omit [Nontrivial H] in
theorem faithfulTensorHom_mem (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (a : Algebra (spatialProductAlgebra M D)) :
    faithfulTensorHom M D a ∈ spatialProductAlgebra (faithfulCyclicAlgebra M) D := by
  let P := spatialProductAlgebra M D
  let N := spatialProductAlgebra (faithfulCyclicAlgebra M) D
  let B : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    (M.toStarSubalgebra.map (spatialLeft (H := H) (K := K))) ⊔
      (D.toStarSubalgebra.map (spatialRight (H := H) (K := K)))
  have hBM : B ≤ P.toStarSubalgebra := subset_generatedVonNeumannAlgebra B
  have hB := faithfulTensorHom_generators_map_le M D
  have hBN (b : B) : faithfulTensorHom M D ⟨b.val, hBM b.property⟩ ∈ N := by
    obtain ⟨c, hc, heq⟩ := hB b.property
    have hcb : c = (⟨b.val, hBM b.property⟩ : Algebra P) := Subtype.ext heq
    change faithfulTensorHom M D c ∈ N at hc
    simpa only [hcb] using hc
  exact boundedWeakNormal_maps_generated P (faithfulTensorHom M D)
    (faithfulTensorHom_boundedWeakNormal M D) B hBM le_rfl N hBN a

theorem faithfulTensorHom_generated_range (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) :
    generatedVonNeumannAlgebra (faithfulTensorHom M D).range =
      spatialProductAlgebra (faithfulCyclicAlgebra M) D := by
  apply le_antisymm
  · apply generatedVonNeumannAlgebra_le_of_le
    rintro _ ⟨a, rfl⟩
    exact faithfulTensorHom_mem M D a
  · apply generatedVonNeumannAlgebra_le_of_le
    apply sup_le
    · rintro _ ⟨m, hm, rfl⟩
      obtain ⟨a, ha⟩ := faithfulCyclicHom_surjective M m hm
      apply subset_generatedVonNeumannAlgebra
      refine ⟨⟨spatialLeft a.val, spatialLeft_mem_product M D a.property⟩, ?_⟩
      exact (faithfulTensorHom_left M D a).trans
        (congrArg (spatialLeft (K := K)) ha)
    · rintro _ ⟨d, hd, rfl⟩
      apply subset_generatedVonNeumannAlgebra
      exact ⟨⟨spatialRight d, spatialRight_mem_product M D hd⟩,
        faithfulTensorHom_right M D ⟨d, hd⟩⟩

def faithfulTensorEquiv (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) :
    Algebra (spatialProductAlgebra M D) ≃⋆ₐ[ℂ]
      Algebra (spatialProductAlgebra (faithfulCyclicAlgebra M) D) :=
  (boundedWeakNormalEquiv (spatialProductAlgebra M D) (faithfulTensorHom M D)
    (faithfulTensorHom_injective M D) (faithfulTensorHom_boundedWeakNormal M D)).trans
      (vonNeumannAlgebraEquivOfEq (faithfulTensorHom_generated_range M D))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalTwoStateAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # The two-state matrix algebra for a specified normal representation change -/

namespace KadisonKastler

open Generator

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)

variable (hθ : BoundedWeakNormal M (N.toStarSubalgebra.subtype.comp θ.toStarAlgHom))

attribute [-instance] CommMagma.to_isCommutative in
def normalTwoStateEquiv : CStarMatrix (Fin 2) (Fin 2) (Algebra M) ≃⋆ₐ[ℂ]
    Algebra (normalTwoStateAlgebra θ) :=
  (matrixAlgebraEquiv M).trans (normalPairEquiv (matrixVonNeumann (ι := Fin 2) M)
    (normalMatrixRepresentation θ) (normalMatrixRepresentation_boundedWeakNormal θ hθ))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalTwoStateState
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # The diagonal state in the normal two-representation matrix algebra -/

namespace KadisonKastler

open Generator

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
  (hθ : BoundedWeakNormal M (N.toStarSubalgebra.subtype.comp θ.toStarAlgHom))
  (Ω : H) (ξ : K)

def normalTwoStateProjection (i : Fin 2) : Algebra (normalTwoStateAlgebra θ) :=
  normalTwoStateEquiv θ hθ (matrixSlot i i 1)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialModularResolution
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Tracial specialization of the constructed modular operators

For a tracial vector state the group is the identity on a dense algebra
orbit. Its normalization clause is therefore unconditional. The polar
conjugation acts by adjoint and gives the right multiplication operators.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))
  (htrace : ∀ a b : Algebra M,
    inner ℂ Ω ((a.val * b.val) Ω) = inner ℂ Ω ((b.val * a.val) Ω))

include htrace

variable [TopologicalSpace.SeparableSpace H]

/-- A faithful tracial cyclic representation has the trivial modular group. -/
theorem modularStrongGroup_tracial (t : Multiplicative ℝ) :
    modularStrongGroup J Ω hsep hcyc t = 1 := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro ξ
  change (modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H) ξ = ξ
  apply hcyc.induction_on (p := fun ξ =>
    (modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H) ξ = ξ) ξ
  · exact isClosed_eq (modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H).continuous continuous_id
  · intro a
    exact modularStrongGroup_fixes_centralizer_vector J Ω hsep hcyc t.toAdd a (htrace a)

end

end KadisonKastler

end OAI
end


