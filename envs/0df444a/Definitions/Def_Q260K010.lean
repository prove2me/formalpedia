-- Prove2me | Definitions.Def_Q260K010
-- name    : Q260K010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:41:57.395142+00:00
-- url     : https://prove2.me/theorems/88413f4f-2868-44f8-8199-b625088a4093
-- title:
--   Definitions bundle Q260K010 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 191 declarations of OpenAI's Lean: 54 definitions, 3 inductive types or structures, 3 instances and 131 theorems. The definitions and types are `OAI.Generator.orthonormalMatrixUnits`, `OAI.HochschildMatrixSystems.MatrixSystem.signedPermutation`, `OAI.HochschildMatrixSystems.MatrixSystem.signedPermutationGroup`, `OAI.HochschildMatrixSystems.MatrixSystem.signedPermutationUnitary`, `OAI.KadisonKastler.FaithfulTracialState.toPositiveLinearMap`, `OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily`, `OAI.KadisonKastler.ScalarBoundaryMean`, `OAI.KadisonKastler.ScalarInvariantMean.algebraMean`, `OAI.KadisonKastler.ScalarInvariantMean.operator`, `OAI.KadisonKastler.ScalarInvariantMean.operatorMean`, `OAI.KadisonKastler.ScalarOperatorKernel`, `OAI.KadisonKastler.ScalarOperatorKernel.CoherentCore`, `OAI.KadisonKastler.ScalarOperatorKernel.CoherentCore.conjugateFunctional`, `OAI.KadisonKastler.ScalarOperatorKernel.CoherentCore.coreLinearMap`, `OAI.KadisonKastler.ScalarOperatorKernel.CoherentCore.coreVector`, `OAI.KadisonKastler.ScalarOperatorKernel.CoherentCore.extendedFunctional`, `OAI.KadisonKastler.ScalarOperatorKernel.CoherentCore.toOperator`, `OAI.KadisonKastler.ScalarOperatorKernel.reconstructedOperator`, `OAI.KadisonKastler.ScalarOperatorKernel.toContinuous`, `OAI.KadisonKastler.ScalarOperatorKernel.toLinear`, `OAI.KadisonKastler.TraceNullSequence`, `OAI.KadisonKastler.TraceStateHilbert`, `OAI.KadisonKastler.TracialSequenceQuotient`, `OAI.KadisonKastler.UniformMeasurableOperators.coefficient`, `OAI.KadisonKastler.UniformMeasurableOperators.coefficientFamily`, `OAI.KadisonKastler.UniformMeasurableOperators.meanCoefficient`, `OAI.KadisonKastler.UniformMeasurableOperators.meanKernel`, `OAI.KadisonKastler.WeakOperatorRepresentative.asUniformFamily`, `OAI.KadisonKastler.WeakOperatorRepresentative.coefficient`, `OAI.KadisonKastler.WeakOperatorRepresentative.scalarKernel`, `OAI.KadisonKastler.ambientAlgebraFamily`, `OAI.KadisonKastler.instPartialOrderTracialSequenceQuotient`, `OAI.KadisonKastler.instPartialOrderTracialSequenceQuotient_1`, `OAI.KadisonKastler.instPartialOrderTracialSequenceQuotient_2`, `OAI.KadisonKastler.scalarBoundaryModule`, `OAI.KadisonKastler.scalarBoundaryTranslate`, `OAI.KadisonKastler.scalarInfinityConst`, `OAI.KadisonKastler.scalarInfinityMul`, `OAI.KadisonKastler.scalarInfinityPullback`, `OAI.KadisonKastler.traceNullClosedIdeal` and 17 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundedHochschild_SignedMatrixUnitaries`, `FactorGeneration_Dimension`, `FactorGeneration_HilbertLimits`, `FactorGeneration_LocalizedStates`, `FactorGeneration_NormalTrace`, `FactorGeneration_OperatorLimits`, `FactorGeneration_SpectralStates`, `KadisonKastler_BoundaryBoundedTransport`, `KadisonKastler_CoreKernelOperator`, `KadisonKastler_FaithfulTraceGNS`, `KadisonKastler_InvariantOperatorMean`, `KadisonKastler_KernelReconstruction`, `KadisonKastler_OrthonormalMatrixUnits`, `KadisonKastler_RegularCoreMatrixData`, `KadisonKastler_ScalarBoundaryMean`, `KadisonKastler_ScalarMeanCoefficients`, `KadisonKastler_ScalarOperatorKernel`, `KadisonKastler_SubalgebraInvariantMean`, `KadisonKastler_TracialCauchySchwarz`, `KadisonKastler_TracialDiagonalLimit`, `KadisonKastler_TracialProducts`, `KadisonKastler_TracialQuotientCompleteness`, `KadisonKastler_TracialQuotientRepresentation`, `KadisonKastler_TracialQuotientVonNeumann`, `KadisonKastler_TracialSequenceIdeal`, `KadisonKastler_TracialSequenceQuotient`, `KadisonKastler_TracialSequenceState`, `KadisonKastler_TwoRatioReindex`, `KadisonKastler_TypeICyclicRepresentation`, `KadisonKastler_VaryingSequence`, `KadisonKastler_WeakOperatorCoefficients`.
--
--   **Imports.** It imports the bundles `Q260K000`, `Q260K001`, `Q260K002`, `Q260K003` and `Q260K004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K017`, `Q260K018`, `Q260K019`, `Q260K020` and `Q260K055`; the statements `OAI.KadisonKastler.ScalarInvariantMean.algebraMean_translate` and `OAI_KadisonKastler_rankFieldCoordinateBorel`; the proofs of `OAI_KadisonKastler_commonRankOperatorField_action`, `OAI.KadisonKastler.exists_near_algebra_of_finite_orbit_bound`, `OAI.KadisonKastler.opNorm_le_of_finite_covariance_families` and `OAI_KadisonKastler_rankFieldCoordinateBorel`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Rat
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
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
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
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
import Mathlib.Data.Nat.Find
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Nat
import Mathlib.Logic.Equiv.Sum
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
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
import Definitions.Def_Q260K000
import Definitions.Def_Q260K001
import Definitions.Def_Q260K002
import Definitions.Def_Q260K003
import Definitions.Def_Q260K004

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_SignedMatrixUnitaries
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite group of signed permutation unitaries in a matrix system. -/

noncomputable section

open scoped BigOperators

namespace HochschildMatrixSystems
namespace MatrixSystem

variable {M : Type*} [CStarAlgebra M] {n : ℕ} (E : MatrixSystem M n)

lemma signScalar_xor (a b : Bool) : signScalar (a ^^ b) = signScalar a * signScalar b := by
  cases a <;> cases b <;> norm_num [signScalar]

def signedPermutation (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) : M :=
  ∑ i, signScalar (s i) • E.entry (σ i) i

lemma signedPermutation_one : E.signedPermutation 1 (fun _ => false) = 1 := by
  simpa only [signedPermutation, signScalar, Bool.false_eq_true, ↓reduceIte,
    one_smul, Equiv.Perm.one_apply] using E.sum_diagonal

lemma signedPermutation_mul (σ τ : Equiv.Perm (Fin n)) (s t : Fin n → Bool) :
    E.signedPermutation σ s * E.signedPermutation τ t =
      E.signedPermutation (σ * τ) (fun i => s (τ i) ^^ t i) := by
  classical
  simp only [signedPermutation, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm,
    E.entry_mul, smul_ite, smul_zero]
  simp [signScalar_xor, Equiv.Perm.mul_apply]

lemma signedPermutation_star (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) :
    star (E.signedPermutation σ s) =
      E.signedPermutation σ⁻¹ (fun i => s (σ⁻¹ i)) := by
  classical
  simp only [signedPermutation, star_sum, star_smul, signScalar_star, E.star_entry]
  apply Fintype.sum_equiv σ _ _
  intro i
  simp

lemma signedPermutation_mem_unitary (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) :
    E.signedPermutation σ s ∈ unitary M := by
  constructor
  · rw [E.signedPermutation_star, E.signedPermutation_mul, inv_mul_cancel]
    simpa using E.signedPermutation_one
  · rw [E.signedPermutation_star, E.signedPermutation_mul, mul_inv_cancel]
    simpa only [Bool.xor_self] using E.signedPermutation_one

def signedPermutationUnitary (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) : unitary M :=
  ⟨E.signedPermutation σ s, E.signedPermutation_mem_unitary σ s⟩

/-- The actual finite subgroup used in the matrix separability homotopy. -/
def signedPermutationGroup : Subgroup (unitary M) where
  carrier := Set.range (fun p : Equiv.Perm (Fin n) × (Fin n → Bool) =>
    E.signedPermutationUnitary p.1 p.2)
  one_mem' := ⟨(1, fun _ => false), Subtype.ext E.signedPermutation_one⟩
  mul_mem' := by
    rintro _ _ ⟨⟨σ, s⟩, rfl⟩ ⟨⟨τ, t⟩, rfl⟩
    exact ⟨(σ * τ, fun i => s (τ i) ^^ t i), Subtype.ext (E.signedPermutation_mul σ τ s t).symm⟩
  inv_mem' := by
    rintro _ ⟨⟨σ, s⟩, rfl⟩
    exact ⟨(σ⁻¹, fun i => s (σ⁻¹ i)), Subtype.ext (E.signedPermutation_star σ s).symm⟩

instance signedPermutationGroup_finite : Finite E.signedPermutationGroup :=
  (Set.finite_range _).to_subtype

end MatrixSystem
end HochschildMatrixSystems

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_OperatorLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Operator-norm completeness of the manuscript's concrete algebra, derived
from its actual double-commutant property. No quotient completeness is assumed. -/
namespace Tracial

/-! Bounded operator families have weak operator ultralimits. This is proved
from Banach--Alaoglu and Riesz representation, not assumed as compactness. -/
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! Operator-norm balls of an actual von Neumann algebra are compact for the
weak operator topology, using the previously constructed operator ultralimits. -/

theorem weakOperatorBall_isCompact (M : VonNeumannAlgebra H) (C : ℝ) :
    IsCompact (weakOperatorBall M C) := by
  classical
  by_cases hC : 0 ≤ C
  · apply isCompact_iff_ultrafilter_le_nhds'.mpr
    intro ω hω
    let a : (H →WOT[ℂ] H) → M.toStarSubalgebra := fun T =>
      if h : T ∈ weakOperatorBall M C then ⟨T.toCLM,h.1⟩ else 0
    have ha (T : H →WOT[ℂ] H) : ‖a T‖ ≤ C := by
      dsimp [a]
      split_ifs with h
      · exact h.2
      · change ‖(0 : H →L[ℂ] H)‖ ≤ C
        simpa only [norm_zero] using hC
    obtain ⟨T,hT,ht⟩ := exists_weak_operator_ultralimit ω (fun U => (a U).val) C hC ha
    have hm := weak_operator_limit_mem M a T ht
    refine ⟨ContinuousLinearMapWOT.ofCLM T,⟨hm,hT⟩,?_⟩
    have hl : Tendsto (fun U => ContinuousLinearMapWOT.ofCLM (a U).val)
        (ω : Filter (H →WOT[ℂ] H)) (𝓝 (ContinuousLinearMapWOT.ofCLM T)) :=
      ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr ht
    have he : (fun U => ContinuousLinearMapWOT.ofCLM (a U).val) =ᶠ[ω] id := by
      filter_upwards [show ∀ᶠ U in (ω : Filter (H →WOT[ℂ] H)),U ∈ weakOperatorBall M C from hω]
        with U hU
      simp only [a,dite_eq_left hU,ContinuousLinearMapWOT.ofCLM_toCLM,id_eq]
    exact hl.congr' he
  · have he : weakOperatorBall M C=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro T hT
      exact hC ((norm_nonneg _).trans hT.2)
    rw [he]
    exact isCompact_empty

end Tracial

/-! Operator order bounds are closed in the weak operator topology. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_HilbertLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Multiplication and adjoint limits in L2, with the necessary uniform
operator norm bounds stated explicitly. -/

/-! A separating vector for a concrete von Neumann algebra is cyclic for its
commutant. The original representation need not be cyclic for the algebra. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vectorOrbitProjection_commutes (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H)
    (a : S) : (vectorOrbitClosure S ξ).starProjection*a.val=
      a.val*(vectorOrbitClosure S ξ).starProjection := by
  apply starProjection_commutes_of_invariant
  · exact fun y hy => vectorOrbitClosure_invariant S ξ a hy
  · exact fun y hy => vectorOrbitClosure_invariant S ξ (star a) hy

theorem commutant_orbitClosure_eq_top (M : VonNeumannAlgebra H) (ξ : H)
    (hξ : ∀ a : M.toStarSubalgebra,a.val ξ=0 → a=0) :
    vectorOrbitClosure M.commutant.toStarSubalgebra ξ=⊤ := by
  let K := vectorOrbitClosure M.commutant.toStarSubalgebra ξ
  have hQ : K.starProjection ∈ M := by
    have h : K.starProjection ∈ M.commutant.commutant := by
      apply VonNeumannAlgebra.mem_commutant_iff.mpr
      intro a ha
      exact (vectorOrbitProjection_commutes M.commutant.toStarSubalgebra ξ ⟨a,ha⟩).symm
    simpa only [M.commutant_commutant] using h
  have he : (1-K.starProjection) ξ=0 := by
    change ξ-K.starProjection ξ=0
    rw [Submodule.starProjection_eq_self_iff.mpr (mem_vectorOrbitClosure _ _),sub_self]
  have hzero := hξ ⟨1-K.starProjection,M.toStarSubalgebra.sub_mem M.one_mem hQ⟩ he
  have h1 : K.starProjection=1 := by
    have h := congrArg Subtype.val hzero
    exact (sub_eq_zero.mp h).symm
  apply top_unique
  intro y _
  apply Submodule.starProjection_eq_self_iff.mp
  rw [show (vectorOrbitClosure M.commutant.toStarSubalgebra ξ).starProjection=1 from h1]
  rfl

theorem commutant_orbit_dense (M : VonNeumannAlgebra H) (ξ : H)
    (hξ : ∀ a : M.toStarSubalgebra,a.val ξ=0 → a=0) :
    Dense (Set.range (fun a : M.commutant.toStarSubalgebra => a.val ξ)) := by
  intro y
  have h : y ∈ vectorOrbitClosure M.commutant.toStarSubalgebra ξ := by
    rw [commutant_orbitClosure_eq_top M ξ hξ]
    trivial
  exact h

end

/-! Restrict the faithful trace representation to the closure of M times its
trace vector. This constructs a faithful, isometric, cyclic representation on
an actual Hilbert subspace. No Banach predual or WOT-closed image is asserted. -/

/-! A real linear functional continuous for bounded trace-two-norm sequences
is WOT continuous on the unit ball. Closed convex slices of the trace-vector
ball supply the conversion; no identification of the two topologies is assumed. -/
open Filter
open scoped Topology

/-! On a uniformly operator-norm bounded family in a faithfully vector-traced
von Neumann algebra, L2 convergence implies strong and adjoint-strong convergence
in the original Hilbert space. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Archimedean comparison for the constructed dyadic reference projections.
Orthogonal sibling corners supply copies for the finite-algebra shift argument. -/

/-! Finite rounding by actual subset projections. A maximal fitting subset
leaves a remainder smaller in comparison than any unused equivalent piece. -/
namespace Tracial

section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! The dyadic lower cut on projections below p and its normalized faithful monotone supremum, capped at one. -/

theorem dyadicWeight_univ (n : ℕ) : dyadicWeight n Finset.univ=1 := by
  unfold dyadicWeight
  rw [Finset.card_univ,card_dyadicIndex,Nat.cast_pow,Nat.cast_ofNat]
  exact div_self (ne_of_gt (pow_pos (by norm_num : (0 : ℝ)<2) n))

end

/-! Common refinements compare arbitrary dyadic levels. The supremum takes
the exact dyadic value on every reference subset projection, and finite
rounding bounds every projection with an explicit error at each level. -/

/-! Orthogonal lower approximants fit disjoint collections of the reference
pieces. Equivalent complements and finite cancellation enforce the capacity. -/

/-! Orthogonal additivity of the constructed dyadic dimension. Numerical
rounding errors tend to zero; every lower and upper bound uses actual
partial-isometry witnesses in the original finite diffuse factor. -/

end Tracial

/-! Classification of projection comparison by the constructed finite
dimension, and a wrapper for exactly the original IsII1Factor predicate.
No normality or trace-extension claim is made here. -/

/-! Bounds and concrete dyadic upper approximants for the constructed
projection dimension. These finite estimates do not assume continuity. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralStates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Additivity on commuting self-adjoint operators, proved using actual common
spectral refinements. The commutation hypothesis is essential to this proof. -/
open scoped BigOperators

/-! Positive spectral approximants, positivity of the constructed scalar, and
order preservation on commuting self-adjoint operators. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.spectralValueCStar
attribute [local instance] OAI.Generator.Tracial.spectralValueOrder
attribute [local instance] OAI.Generator.Tracial.spectralValuePreorder
attribute [local instance] OAI.Generator.Tracial.spectralValueLE
attribute [local instance] OAI.Generator.Tracial.spectralValueStarOrder
/-- A positive operator has arbitrarily accurate finite positive spectral
approximants preserving its entire commutant. -/
theorem exists_positive_spectral_approximation
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))
      (c : Fin Q.size → ℝ),
      (∀ i, 0 ≤ c i) ∧
      (∀ y : M.toStarSubalgebra, Commute x y → ∀ i, Commute (Q.piece i).val y) ∧
      ‖x-∑ i, (c i : ℂ) • (Q.piece i).val‖ < ε := by
  let I : SpectralInterval x :=
    { proj := ⟨1,IsStarProjection.one _⟩
      lo := 0
      hi := ‖x‖
      lower := by simpa only [one_mul,mul_one,Complex.ofReal_zero,zero_smul,sub_zero] using hx
      upper := (initialSpectralInterval ⟨1,IsStarProjection.one _⟩ x hx.isSelfAdjoint).upper }
  have hI : I.lo ≤ I.hi := norm_nonneg x
  obtain ⟨n,hn⟩ := I.exists_approximant hx.isSelfAdjoint hI ε hε
  let e := (Fintype.equivFin (DyadicIndex n)).symm
  refine ⟨I.partition hx.isSelfAdjoint n,fun i => (I.level hx.isSelfAdjoint n (e i)).lo,?_,?_,?_⟩
  · intro i
    exact (I.level_endpoints hx.isSelfAdjoint hI n (e i)).1
  · intro y hy i
    exact I.partition_commutes hx.isSelfAdjoint hy (Commute.one_left y) n i
  · change ‖x-∑ i, ((I.level hx.isSelfAdjoint n (e i)).lo : ℂ) •
        (I.level hx.isSelfAdjoint n (e i)).proj.val‖ < ε
    rw [Equiv.sum_comp e (fun i => ((I.level hx.isSelfAdjoint n i).lo : ℂ) •
      (I.level hx.isSelfAdjoint n i).proj.val)]
    change ‖1*x*1-∑ i, ((I.level hx.isSelfAdjoint n i).lo : ℂ) •
      (I.level hx.isSelfAdjoint n i).proj.val‖ < ε at hn
    simpa only [one_mul,mul_one] using hn

end

/-! A nonzero positive operator dominates a positive multiple of an actual
nonzero spectral projection. This proves faithfulness without linearity. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.spectralFaithfulCStar
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulOrder
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulPreorder
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulLE
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulStarOrder
theorem positive_spectral_cut_domination
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (t : ℝ) :
    (t : ℂ) • (cornerSpectralCut ⟨1,IsStarProjection.one _⟩ x t).val ≤ x := by
  let p : AlgebraProjection M := ⟨1,IsStarProjection.one _⟩
  let q := cornerSpectralCut p x t
  have hl : 0 ≤ q.val*x*q.val-(t : ℂ) • q.val := cornerSpectralCut_lower p x hx.isSelfAdjoint t
  have hr := star_left_conjugate_nonneg hx (1-q.val)
  rw [star_sub,star_one,q.property.isSelfAdjoint.star_eq] at hr
  have hsum := add_nonneg hl hr
  have he := cornerSpectralPartition_pinch p x hx.isSelfAdjoint t
  rw [cornerSpectralPartition,CornerPartition.binary_pinch] at he
  change q.val*x*q.val+(1-q.val)*x*(1-q.val)=1*x*1 at he
  simp only [one_mul,mul_one] at he
  have he' : q.val*x*q.val-(t : ℂ) • q.val+(1-q.val)*x*(1-q.val)=x-(t : ℂ) • q.val := by
    rw [show q.val*x*q.val-(t : ℂ) • q.val+(1-q.val)*x*(1-q.val)=
      (q.val*x*q.val+(1-q.val)*x*(1-q.val))-(t : ℂ) • q.val by abel,he]
  rw [he'] at hsum
  exact sub_nonneg.mp hsum

end

/-! Unitary conjugacy preserves projection dimension and its constructed
spectral extension. No trace identity is assumed. -/
open scoped BigOperators

/-! The constructed scalar agrees on x*x and xx*, by an actual unitary polar
decomposition. This is a quadratic identity, not unrestricted additivity. -/
open scoped CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Localization of actual signed vector/dimension values. Fixed strict
sublevel sets, rather than a limiting strict inequality, supply Zorn bounds. -/
open Filter
open scoped Topology

/-! Tight multiplicative localization of an actual Hilbert vector functional
against the constructed projection dimension. The corner is constructed. -/

/-! Positive spectral approximants inside an actual projection corner, and
extension of localized projection inequalities to positive operators. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.cornerValueCStar
attribute [local instance] OAI.Generator.Tracial.cornerValueOrder
local instance cornerValuePreorder_rab37e7_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.cornerValueLE
attribute [local instance] OAI.Generator.Tracial.cornerValueStarOrder
/-- A positive operator supported by p is approximated inside that same corner. -/
theorem exists_positive_corner_spectral_approximation
    (p : AlgebraProjection M) (x : M.toStarSubalgebra) (hx : 0 ≤ x)
    (hpx : p.val*x=x) (ε : ℝ) (hε : 0<ε) :
    ∃ (Q : CornerPartition p) (c : Fin Q.size → ℝ),
      (∀ i, 0 ≤ c i) ∧ (∀ i, Commute (Q.piece i).val x) ∧
      ‖x-∑ i, (c i : ℂ) • (Q.piece i).val‖ < ε := by
  have hxp : x*p.val=x := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq,hx.isSelfAdjoint.star_eq]
      using congrArg star hpx
  let I : SpectralInterval x :=
    { proj := p
      lo := 0
      hi := ‖x‖
      lower := by simpa only [hpx,hxp,Complex.ofReal_zero,zero_smul,sub_zero] using hx
      upper := (initialSpectralInterval p x hx.isSelfAdjoint).upper }
  have hI : I.lo ≤ I.hi := norm_nonneg x
  obtain ⟨n,hn⟩ := I.exists_approximant hx.isSelfAdjoint hI ε hε
  let e := (Fintype.equivFin (DyadicIndex n)).symm
  refine ⟨I.partition hx.isSelfAdjoint n,fun i => (I.level hx.isSelfAdjoint n (e i)).lo,?_,?_,?_⟩
  · intro i
    exact (I.level_endpoints hx.isSelfAdjoint hI n (e i)).1
  · intro i
    exact I.partition_commutes hx.isSelfAdjoint (Commute.refl x) (hpx.trans hxp.symm) n i
  · change ‖x-∑ i, ((I.level hx.isSelfAdjoint n (e i)).lo : ℂ) •
        (I.level hx.isSelfAdjoint n (e i)).proj.val‖ < ε
    rw [Equiv.sum_comp e (fun i => ((I.level hx.isSelfAdjoint n i).lo : ℂ) •
      (I.level hx.isSelfAdjoint n i).proj.val)]
    change ‖p.val*x*p.val-∑ i, ((I.level hx.isSelfAdjoint n i).lo : ℂ) •
      (I.level hx.isSelfAdjoint n i).proj.val‖ < ε at hn
    simpa only [hpx,hxp] using hn

end

/-! Projection localization yields actual positive-operator inequalities for
bounded linear functionals, and a nearly cyclic functional on the corner. -/
open scoped BigOperators CStarAlgebra

/-! An actual positive normalized vector functional with arbitrarily small
multiplicative failure of cyclicity on a nonzero corner. No trace is assumed. -/
open scoped CStarAlgebra

/-! A full finite matrix partition can be rebased into every nonzero corner.
The legs are constructed partial isometries, not assumed matrix units. -/
open scoped BigOperators

/-! Extension of a vector functional through actual matrix-partition legs.
Finite coefficient identities transfer the corner quadratic inequality. -/
open scoped BigOperators CStarAlgebra

/-! Globally defined positive unital linear functionals with arbitrarily small multiplicative quadratic trace error. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

local instance stateDimensionCStar_rab37e7_1 : CStarAlgebra M.toStarSubalgebra := {}
attribute [local instance] OAI.Generator.Tracial.stateDimensionOrder
local instance stateDimensionPreorder_rab37e7_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.stateDimensionLE
attribute [local instance] OAI.Generator.Tracial.stateDimensionStarOrder
theorem algebraProjection_nonneg (p : AlgebraProjection M) : 0 ≤ p.val := by
  have h : star p.val*p.val=p.val := by
    rw [p.property.isSelfAdjoint.star_eq,p.property.isIdempotentElem.eq]
  rw [← h]
  exact star_mul_self_nonneg _

theorem tracialFunctional_equivalent (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    {p q : AlgebraProjection M} (h : p.Equivalent q) : φ p.val=φ q.val := by
  obtain ⟨v,hv,ht⟩ := h
  rw [← hv,← ht,← v.initial]
  exact htrace (star v.val) v.val

theorem positiveFunctional_projection_mono (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (hpos : ∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re)
    {p q : AlgebraProjection M} (h : p ≤ q) : (φ p.val).re ≤ (φ q.val).re := by
  have hr := hpos (AlgebraProjection.remainder p q h).val
    (algebraProjection_nonneg _)
  change 0 ≤ (φ (q.val-p.val)).re at hr
  rw [map_sub,Complex.sub_re] at hr
  linarith

theorem tracialFunctional_subequivalent (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (hpos : ∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re)
    (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    {p q : AlgebraProjection M} (h : p.Subequivalent q) : (φ p.val).re ≤ (φ q.val).re := by
  obtain ⟨v,hv,ht⟩ := h
  have he := tracialFunctional_equivalent φ htrace
    (show p.Equivalent v.target from ⟨v,hv,rfl⟩)
  rw [he]
  exact positiveFunctional_projection_mono φ hpos ht

end

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryBoundedTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded transport fields and the correction step

For an action on a C-star algebra, the transport fields are actual bounded
unitary families.  An equivariant bimodule mean therefore gives the quadratic
step in the complete metric space of unitary families.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction CStarAlgebra

noncomputable section

variable {G B : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [CStarAlgebra B]

local instance boundaryBoundedComplete_rab37e7_1 : CompleteSpace (unitary (G →ᵇ B)) :=
  isClosed_unitary.completeSpace_coe
attribute [local instance] OAI.KadisonKastler.boundaryBoundedStarOrder
omit [Group G] [DiscreteTopology G] in
@[simp]
theorem boundaryConstant_apply (b : B) (t : G) :
    boundaryConstant (G := G) b t = b := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarBoundaryMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The scalar boundary mean on actual L-infinity classes

The source is the bounded family of L-infinity sections indexed by the
countable discrete group. Multiplication and nonsingular pullback are
defined on the actual almost-everywhere classes. The scalar
conditional-expectation property includes the module and action identities.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {D : Type*} [MeasurableSpace D] {μ : Measure D}

/-- Constant scalar functions as actual L-infinity classes. -/
def scalarInfinityConst (μ : Measure D) (z : ℂ) : ScalarLInfinity μ :=
  (memLp_top_const z).toLp (fun _ => z)

/-- The essential norm bounds any representative almost everywhere. -/
theorem scalarInfinity_ae_norm_le (f : ScalarLInfinity μ) :
    ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ := by
  have h := ae_le_lpNorm_exponent_top (Lp.memLp f)
  rwa [← toReal_eLpNorm (Lp.aestronglyMeasurable f), ← Lp.norm_def] at h

/-- Pointwise multiplication descends to L-infinity classes. -/
def scalarInfinityMul (f g : ScalarLInfinity μ) : ScalarLInfinity μ :=
  (MeasureTheory.MemLp.mul (hφ := (Lp.memLp f)) (hf := (Lp.memLp g))).toLp (fun x => f x * g x)

theorem scalarInfinityMul_ae (f g : ScalarLInfinity μ) :
    scalarInfinityMul f g =ᵐ[μ] fun x => f x * g x := MemLp.coeFn_toLp _

theorem norm_scalarInfinityMul_le (f g : ScalarLInfinity μ) :
    ‖scalarInfinityMul f g‖ ≤ ‖f‖ * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalarInfinityMul_ae f g, scalarInfinity_ae_norm_le f] with x hfg hf
  rw [hfg, norm_mul]
  exact mul_le_mul_of_nonneg_right hf (norm_nonneg _)

section Pullback

variable [IsFiniteMeasure μ] {E : Type*} [MeasurableSpace E]
  {ν : Measure E} [IsFiniteMeasure ν]

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
/-- Nonsingular pullback preserves essential boundedness. -/
theorem memLp_scalarInfinity_comp (f : ScalarLInfinity ν) (T : D → E)
    (hT : Measure.QuasiMeasurePreserving T μ ν) : MemLp (fun x => f (T x)) ⊤ μ :=
  memLp_top_of_bound ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving hT)
    ‖f‖ (hT.ae (scalarInfinity_ae_norm_le f))

def scalarInfinityPullback (T : D → E) (hT : Measure.QuasiMeasurePreserving T μ ν)
    (f : ScalarLInfinity ν) : ScalarLInfinity μ :=
  (memLp_scalarInfinity_comp f T hT).toLp (fun x => f (T x))

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
theorem scalarInfinityPullback_ae (T : D → E)
    (hT : Measure.QuasiMeasurePreserving T μ ν) (f : ScalarLInfinity ν) :
    scalarInfinityPullback T hT f =ᵐ[μ] fun x => f (T x) := MemLp.coeFn_toLp _

omit [IsFiniteMeasure ν] in
theorem norm_scalarInfinityPullback_le (T : D → E)
    (hT : Measure.QuasiMeasurePreserving T μ ν) (f : ScalarLInfinity ν) :
    ‖scalarInfinityPullback T hT f‖ ≤ ‖f‖ := by
  have hb : ∀ᵐ x ∂μ, ‖scalarInfinityPullback T hT f x‖ ≤ ‖f‖ := by
    filter_upwards [scalarInfinityPullback_ae T hT f,
      hT.ae (scalarInfinity_ae_norm_le f)] with x hx hb
    rwa [hx]
  simpa using Lp.norm_le_of_ae_bound (norm_nonneg f) hb

end Pullback

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [IsFiniteMeasure μ]

/-- The scalar module action on a bounded family of L-infinity sections. -/
def scalarBoundaryModule (b : ScalarLInfinity μ) (F : G →ᵇ ScalarLInfinity μ) :
    G →ᵇ ScalarLInfinity μ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun t => scalarInfinityMul b (F t)) (‖b‖ * ‖F‖) (fun t =>
      (norm_scalarInfinityMul_le b (F t)).trans
        (mul_le_mul_of_nonneg_left (F.norm_coe_le_norm t) (norm_nonneg b)))

/-- Simultaneous inverse translation of the group and boundary coordinates. -/
def scalarBoundaryTranslate (α : NonsingularAction G D μ) (g : G)
    (F : G →ᵇ ScalarLInfinity μ) : G →ᵇ ScalarLInfinity μ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun t => scalarInfinityPullback (α.toPerm g⁻¹) (α.quasi g⁻¹) (F (g⁻¹ * t)))
    ‖F‖ (fun _t => (norm_scalarInfinityPullback_le _ _ _).trans (F.norm_coe_le_norm _))

/-- Scalar equivariant conditional expectation in the section model of
L-infinity(G × D). These are the exact structural scalar conclusions
of Adams–Elliott–Giordano, Theorem 3.4; existence is not asserted here. -/
structure ScalarBoundaryMean (α : NonsingularAction G D μ) where
  toCLM : (G →ᵇ ScalarLInfinity μ) →L[ℂ] ScalarLInfinity μ
  map_one : toCLM (BoundedContinuousFunction.const G (scalarInfinityConst μ 1)) =
    scalarInfinityConst μ 1
  norm_le : ∀ F, ‖toCLM F‖ ≤ ‖F‖
  positive : ∀ F, (∀ g, ∀ᵐ x ∂μ, (F g x).im = 0 ∧ 0 ≤ (F g x).re) →
    ∀ᵐ x ∂μ, (toCLM F x).im = 0 ∧ 0 ≤ (toCLM F x).re
  module_map : ∀ b F, toCLM (scalarBoundaryModule b F) = scalarInfinityMul b (toCLM F)
  equivariant : ∀ g F, toCLM (scalarBoundaryTranslate α g F) =
    scalarInfinityPullback (α.toPerm g⁻¹) (α.quasi g⁻¹) (toCLM F)


end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarMeanCoefficients
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Matrix coefficients of the scalar boundary mean

A uniformly bounded family of weakly measurable operators gives a
sesquilinear family of scalar L-infinity classes. Applying the scalar
conditional expectation preserves its algebraic identities and bounds.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*}
  [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace UniformMeasurableOperators

variable (T : UniformMeasurableOperators G D H μ)

/-- A scalar matrix coefficient is an actual L-infinity class. -/
def coefficient (g : G) (ξ η : H) : ScalarLInfinity μ :=
  (memLp_top_of_bound ((T.measurable g ξ).const_inner)
    (T.bound * ‖ξ‖ * ‖η‖) (Eventually.of_forall fun x => by
      calc
        ‖inner ℂ η (T.eval g x ξ)‖ ≤ ‖η‖ * ‖T.eval g x ξ‖ := norm_inner_le_norm _ _
        _ ≤ ‖η‖ * (T.bound * ‖ξ‖) := mul_le_mul_of_nonneg_left
          ((T.eval g x).le_opNorm ξ |>.trans
            (mul_le_mul_of_nonneg_right (T.norm_le g x) (norm_nonneg ξ))) (norm_nonneg η)
        _ = _ := by ring)).toLp (fun x => inner ℂ η (T.eval g x ξ))

@[simp]
theorem coefficient_ae (g : G) (ξ η : H) :
    T.coefficient g ξ η =ᵐ[μ] fun x => inner ℂ η (T.eval g x ξ) := MemLp.coeFn_toLp _

section Finite

variable [IsFiniteMeasure μ]

theorem norm_coefficient_le (g : G) (ξ η : H) :
    ‖T.coefficient g ξ η‖ ≤ T.bound * ‖ξ‖ * ‖η‖ := by
  suffices hb : ∀ᵐ x ∂μ, ‖T.coefficient g ξ η x‖ ≤ T.bound * ‖ξ‖ * ‖η‖ by
    simpa using Lp.norm_le_of_ae_bound
      (mul_nonneg (mul_nonneg T.bound_nonneg (norm_nonneg ξ)) (norm_nonneg η)) hb
  filter_upwards [T.coefficient_ae g ξ η] with x hx
  rw [hx]
  calc
    _ ≤ ‖η‖ * ‖T.eval g x ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖η‖ * (T.bound * ‖ξ‖) := mul_le_mul_of_nonneg_left
      ((T.eval g x).le_opNorm ξ |>.trans
        (mul_le_mul_of_nonneg_right (T.norm_le g x) (norm_nonneg ξ))) (norm_nonneg η)
    _ = _ := by ring

end Finite

theorem coefficient_add_left (g : G) (ξ ζ η : H) :
    T.coefficient g (ξ + ζ) η = T.coefficient g ξ η + T.coefficient g ζ η := by
  apply Lp.ext
  filter_upwards [T.coefficient_ae g (ξ + ζ) η, T.coefficient_ae g ξ η,
    T.coefficient_ae g ζ η, Lp.coeFn_add (T.coefficient g ξ η) (T.coefficient g ζ η)]
      with x ha hb hc hd
  simp only [Pi.add_apply] at hd
  rw [ha, hd, hb, hc, map_add, inner_add_right]

theorem coefficient_smul_left (g : G) (c : ℂ) (ξ η : H) :
    T.coefficient g (c • ξ) η = c • T.coefficient g ξ η := by
  apply Lp.ext
  filter_upwards [T.coefficient_ae g (c • ξ) η, T.coefficient_ae g ξ η,
    Lp.coeFn_smul c (T.coefficient g ξ η)] with x ha hb hc
  simp only [Pi.smul_apply] at hc
  rw [ha, hc, hb, map_smul, inner_smul_right]
  rfl

theorem coefficient_add_right (g : G) (ξ η ζ : H) :
    T.coefficient g ξ (η + ζ) = T.coefficient g ξ η + T.coefficient g ξ ζ := by
  apply Lp.ext
  filter_upwards [T.coefficient_ae g ξ (η + ζ), T.coefficient_ae g ξ η,
    T.coefficient_ae g ξ ζ, Lp.coeFn_add (T.coefficient g ξ η) (T.coefficient g ξ ζ)]
      with x ha hb hc hd
  simp only [Pi.add_apply] at hd
  rw [ha, hd, hb, hc, inner_add_left]

theorem coefficient_smul_right (g : G) (c : ℂ) (ξ η : H) :
    T.coefficient g ξ (c • η) = star c • T.coefficient g ξ η := by
  apply Lp.ext
  filter_upwards [T.coefficient_ae g ξ (c • η), T.coefficient_ae g ξ η,
    Lp.coeFn_smul (star c) (T.coefficient g ξ η)] with x ha hb hc
  simp only [Pi.smul_apply] at hc
  rw [ha, hc, hb, inner_smul_left]
  rfl

variable [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]

/-- All group coordinates of a coefficient form a uniformly bounded
family, the precise source space of the scalar mean. -/
def coefficientFamily (ξ η : H) : G →ᵇ ScalarLInfinity μ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => T.coefficient g ξ η) (T.bound * ‖ξ‖ * ‖η‖)
    (fun g => T.norm_coefficient_le g ξ η)

@[simp]
theorem coefficientFamily_apply (ξ η : H) (g : G) :
    T.coefficientFamily ξ η g = T.coefficient g ξ η := rfl

theorem norm_coefficientFamily_le (ξ η : H) :
    ‖T.coefficientFamily ξ η‖ ≤ T.bound * ‖ξ‖ * ‖η‖ :=
  (BoundedContinuousFunction.norm_le
    (mul_nonneg (mul_nonneg T.bound_nonneg (norm_nonneg ξ)) (norm_nonneg η))).mpr
    (fun g => T.norm_coefficient_le g ξ η)

theorem coefficientFamily_add_left (ξ ζ η : H) :
    T.coefficientFamily (ξ + ζ) η = T.coefficientFamily ξ η + T.coefficientFamily ζ η := by
  apply BoundedContinuousFunction.ext
  intro g
  exact T.coefficient_add_left g ξ ζ η

theorem coefficientFamily_smul_left (c : ℂ) (ξ η : H) :
    T.coefficientFamily (c • ξ) η = c • T.coefficientFamily ξ η := by
  apply BoundedContinuousFunction.ext
  intro g
  exact T.coefficient_smul_left g c ξ η

theorem coefficientFamily_add_right (ξ η ζ : H) :
    T.coefficientFamily ξ (η + ζ) = T.coefficientFamily ξ η + T.coefficientFamily ξ ζ := by
  apply BoundedContinuousFunction.ext
  intro g
  exact T.coefficient_add_right g ξ η ζ

theorem coefficientFamily_smul_right (c : ℂ) (ξ η : H) :
    T.coefficientFamily ξ (c • η) = star c • T.coefficientFamily ξ η := by
  apply BoundedContinuousFunction.ext
  intro g
  exact T.coefficient_smul_right g c ξ η

variable [Group G]

/-- Apply the scalar expectation to the actual coefficient family. -/
def meanCoefficient {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
    (ξ η : H) : ScalarLInfinity μ := m.toCLM (T.coefficientFamily ξ η)

theorem norm_meanCoefficient_le {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
    (ξ η : H) : ‖T.meanCoefficient m ξ η‖ ≤ T.bound * ‖ξ‖ * ‖η‖ :=
  (m.norm_le _).trans (T.norm_coefficientFamily_le ξ η)

theorem meanCoefficient_add_left {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
    (ξ ζ η : H) :
    T.meanCoefficient m (ξ + ζ) η = T.meanCoefficient m ξ η + T.meanCoefficient m ζ η := by
  simp only [meanCoefficient, T.coefficientFamily_add_left, map_add]

theorem meanCoefficient_smul_left {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
    (c : ℂ) (ξ η : H) : T.meanCoefficient m (c • ξ) η = c • T.meanCoefficient m ξ η := by
  simp only [meanCoefficient, T.coefficientFamily_smul_left, map_smul]

theorem meanCoefficient_add_right {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
    (ξ η ζ : H) :
    T.meanCoefficient m ξ (η + ζ) = T.meanCoefficient m ξ η + T.meanCoefficient m ξ ζ := by
  simp only [meanCoefficient, T.coefficientFamily_add_right, map_add]

theorem meanCoefficient_smul_right {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
    (c : ℂ) (ξ η : H) : T.meanCoefficient m ξ (c • η) = star c • T.meanCoefficient m ξ η := by
  simp only [meanCoefficient, T.coefficientFamily_smul_right, map_smul]

end UniformMeasurableOperators

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarOperatorKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Simultaneous scalar representatives on a countable complex core

An L-infinity-valued bounded sesquilinear kernel has, almost everywhere,
a genuinely sesquilinear bounded scalar kernel on the rational core.
No uncountable intersection of conull sets is used.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The bounded sesquilinear coefficient data from which an operator
field is reconstructed. The first vector is the input to the operator. -/
structure ScalarOperatorKernel (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (μ : Measure D) where
  coeff : H → H → ScalarLInfinity μ
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ ξ η, ‖coeff ξ η‖ ≤ bound * ‖ξ‖ * ‖η‖
  add_left : ∀ ξ ζ η, coeff (ξ + ζ) η = coeff ξ η + coeff ζ η
  add_right : ∀ ξ η ζ, coeff ξ (η + ζ) = coeff ξ η + coeff ξ ζ
  smul_left : ∀ (c : ℂ) ξ η, coeff (c • ξ) η = c • coeff ξ η
  smul_right : ∀ (c : ℂ) ξ η, coeff ξ (c • η) = star c • coeff ξ η

namespace ScalarOperatorKernel

variable (K : ScalarOperatorKernel H μ)

theorem add_left_ae (ξ ζ η : H) :
    ∀ᵐ x ∂μ, K.coeff (ξ + ζ) η x = K.coeff ξ η x + K.coeff ζ η x := by
  rw [K.add_left]
  exact (Lp.coeFn_add (K.coeff ξ η) (K.coeff ζ η)).mono fun x hx => by
    simpa only [Pi.add_apply] using hx

theorem add_right_ae (ξ η ζ : H) :
    ∀ᵐ x ∂μ, K.coeff ξ (η + ζ) x = K.coeff ξ η x + K.coeff ξ ζ x := by
  rw [K.add_right]
  exact (Lp.coeFn_add (K.coeff ξ η) (K.coeff ξ ζ)).mono fun x hx => by
    simpa only [Pi.add_apply] using hx

theorem smul_left_ae (c : ℂ) (ξ η : H) :
    ∀ᵐ x ∂μ, K.coeff (c • ξ) η x = c * K.coeff ξ η x := by
  rw [K.smul_left]
  exact (Lp.coeFn_smul c (K.coeff ξ η)).mono fun x hx => by
    simpa only [Pi.smul_apply, smul_eq_mul] using hx

theorem smul_right_ae (c : ℂ) (ξ η : H) :
    ∀ᵐ x ∂μ, K.coeff ξ (c • η) x = star c * K.coeff ξ η x := by
  rw [K.smul_right]
  exact (Lp.coeFn_smul (star c) (K.coeff ξ η)).mono fun x hx => by
    simpa only [Pi.smul_apply, smul_eq_mul] using hx

theorem bound_ae (ξ η : H) :
    ∀ᵐ x ∂μ, ‖K.coeff ξ η x‖ ≤ K.bound * ‖ξ‖ * ‖η‖ :=
  (scalarInfinity_ae_norm_le _).mono fun _ hx => hx.trans (K.norm_le ξ η)


/-- Bundle the coefficient identities as a sesquilinear map. -/
def toLinear : H →ₗ[ℂ] H →ₗ⋆[ℂ] ScalarLInfinity μ where
  toFun ξ :=
    { toFun := K.coeff ξ
      map_add' := K.add_right ξ
      map_smul' := fun c η => K.smul_right c ξ η }
  map_add' ξ ζ := by
    apply LinearMap.ext
    intro η
    exact K.add_left ξ ζ η
  map_smul' c ξ := by
    apply LinearMap.ext
    intro η
    exact K.smul_left c ξ η

/-- The L-infinity coefficient map is jointly continuous. -/
def toContinuous : H →L[ℂ] H →L⋆[ℂ] ScalarLInfinity μ :=
  K.toLinear.mkContinuous₂ K.bound K.norm_le

@[simp]
theorem toContinuous_apply (ξ η : H) : K.toContinuous ξ η = K.coeff ξ η := rfl

/-- Agreement on the dense core determines the whole kernel. -/
theorem coeff_eq_of_core (L : ScalarOperatorKernel H μ) (C : RationalComplexCore H)
    (h : ∀ ξ η : C.space, K.coeff ξ η = L.coeff ξ η) :
    ∀ ξ η : H, K.coeff ξ η = L.coeff ξ η := by
  have hd : DenseRange ((↑) : C.space → H) := C.dense.denseRange_val
  have hout : K.toContinuous = L.toContinuous := by
    apply ContinuousLinearMap.ext
    have he : (fun ξ : H => K.toContinuous ξ) = (fun ξ : H => L.toContinuous ξ) := by
      apply hd.equalizer K.toContinuous.continuous L.toContinuous.continuous
      funext ξ
      apply ContinuousLinearMap.ext
      have hi := hd.equalizer (K.toContinuous ξ).continuous (L.toContinuous ξ).continuous
        (funext fun η => h ξ η)
      exact congrFun hi
    exact congrFun he
  intro ξ η
  exact congrArg (fun F : H →L[ℂ] H →L⋆[ℂ] ScalarLInfinity μ => F ξ η) hout

/-- Pointwise bounded rational sesquilinearity, including the two tests
with multiplication by i that force complex sesquilinearity by continuity. -/
structure CoherentCore (C : RationalComplexCore H) (k : C.space → C.space → ℂ) : Prop where
  add_left : ∀ ξ ζ η, k (ξ + ζ) η = k ξ η + k ζ η
  add_right : ∀ ξ η ζ, k ξ (η + ζ) = k ξ η + k ξ ζ
  rat_left : ∀ (r : ℚ) ξ η, k (r • ξ) η = (r : ℂ) * k ξ η
  rat_right : ∀ (r : ℚ) ξ η, k ξ (r • η) = (r : ℂ) * k ξ η
  I_left : ∀ ξ η, k (C.mulI ξ) η = Complex.I * k ξ η
  I_right : ∀ ξ η, k ξ (C.mulI η) = -Complex.I * k ξ η
  bound : ∀ ξ η, ‖k ξ η‖ ≤ K.bound * ‖ξ‖ * ‖η‖

/-- Countability gives one conull set on which every core identity and
bound holds at once. -/
theorem coherentCore_ae (C : RationalComplexCore H) :
    ∀ᵐ x ∂μ, K.CoherentCore C (fun ξ η => K.coeff (ξ : H) (η : H) x) := by
  let : Countable C.space := C.countable
  have h1 : ∀ᵐ x ∂μ, ∀ ξ ζ η : C.space,
      K.coeff (↑(ξ + ζ)) η x = K.coeff ξ η x + K.coeff ζ η x :=
    ae_all_iff.mpr fun ξ => ae_all_iff.mpr fun ζ => ae_all_iff.mpr fun η =>
      K.add_left_ae ξ ζ η
  have h2 : ∀ᵐ x ∂μ, ∀ ξ η ζ : C.space,
      K.coeff ξ (↑(η + ζ)) x = K.coeff ξ η x + K.coeff ξ ζ x :=
    ae_all_iff.mpr fun ξ => ae_all_iff.mpr fun η => ae_all_iff.mpr fun ζ =>
      K.add_right_ae ξ η ζ
  have h3 : ∀ᵐ x ∂μ, ∀ (r : ℚ) (ξ η : C.space),
      K.coeff (↑(r • ξ)) η x = (r : ℂ) * K.coeff ξ η x := by
    apply ae_all_iff.mpr
    intro r
    apply ae_all_iff.mpr
    intro ξ
    apply ae_all_iff.mpr
    intro η
    simpa only [Submodule.coe_smul, ← Rat.cast_smul_eq_qsmul ℂ] using
      K.smul_left_ae (r : ℂ) ξ η
  have h4 : ∀ᵐ x ∂μ, ∀ (r : ℚ) (ξ η : C.space),
      K.coeff ξ (↑(r • η)) x = (r : ℂ) * K.coeff ξ η x := by
    apply ae_all_iff.mpr
    intro r
    apply ae_all_iff.mpr
    intro ξ
    apply ae_all_iff.mpr
    intro η
    simpa only [Submodule.coe_smul, ← Rat.cast_smul_eq_qsmul ℂ, star_ratCast] using
      K.smul_right_ae (r : ℂ) ξ η
  have h5 : ∀ᵐ x ∂μ, ∀ ξ η : C.space,
      K.coeff (C.mulI ξ) η x = Complex.I * K.coeff ξ η x :=
    ae_all_iff.mpr fun ξ => ae_all_iff.mpr fun η => K.smul_left_ae Complex.I ξ η
  have h6 : ∀ᵐ x ∂μ, ∀ ξ η : C.space,
      K.coeff ξ (C.mulI η) x = -Complex.I * K.coeff ξ η x := by
    apply ae_all_iff.mpr
    intro ξ
    apply ae_all_iff.mpr
    intro η
    simpa only [RationalComplexCore.coe_mulI, Complex.star_def, Complex.conj_I] using
      K.smul_right_ae Complex.I ξ η
  have h7 : ∀ᵐ x ∂μ, ∀ ξ η : C.space,
      ‖K.coeff ξ η x‖ ≤ K.bound * ‖ξ‖ * ‖η‖ :=
    ae_all_iff.mpr fun ξ => ae_all_iff.mpr fun η => K.bound_ae ξ η
  filter_upwards [h1, h2, h3, h4, h5, h6, h7] with x h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end ScalarOperatorKernel

variable [CompleteSpace H] {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]

/-- The scalar boundary mean supplies all data of the bounded operator kernel. -/
def UniformMeasurableOperators.meanKernel (T : UniformMeasurableOperators G D H μ)
    {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α) : ScalarOperatorKernel H μ where
  coeff := T.meanCoefficient m
  bound := T.bound
  bound_nonneg := T.bound_nonneg
  norm_le := T.norm_meanCoefficient_le m
  add_left := T.meanCoefficient_add_left m
  add_right := T.meanCoefficient_add_right m
  smul_left := T.meanCoefficient_smul_left m
  smul_right := T.meanCoefficient_smul_right m

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreKernelOperator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reconstruction of a bounded operator from a coherent core kernel

Riesz representation first reconstructs the image of every vector in the
countable rational core. The complex-linear extension preserves the bound.
-/

namespace KadisonKastler

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : MeasureTheory.Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace ScalarOperatorKernel.CoherentCore

variable {K : ScalarOperatorKernel H μ} {C : RationalComplexCore H}
  {k : C.space → C.space → ℂ} (hk : K.CoherentCore C k)

attribute [local instance] OAI.KadisonKastler.coreKernelRationalNormedSpace
/-- Conjugating the test-vector slot makes it rational-linear. -/
def conjugateFunctional (ξ : C.space) : C.space →ₗ[ℚ] ℂ :=
  ({ toFun := fun η => star (k ξ η)
     map_zero' := by
       have hz : k ξ 0 = 0 := by
         simpa only [zero_smul, Rat.cast_zero, zero_mul] using hk.rat_right 0 ξ 0
       rw [hz, star_zero]
     map_add' := fun η ζ => by rw [hk.add_right, star_add] } : C.space →+ ℂ).toRatLinearMap

theorem conjugateFunctional_bound (ξ η : C.space) :
    ‖hk.conjugateFunctional ξ η‖ ≤ (K.bound * ‖ξ‖) * ‖(η : H)‖ := by
  change ‖star (k ξ η)‖ ≤ (K.bound * ‖ξ‖) * ‖(η : H)‖
  simpa only [norm_star, Submodule.norm_coe] using hk.bound ξ η

theorem conjugateFunctional_mulI (ξ η : C.space) :
    hk.conjugateFunctional ξ (C.mulI η) =
      Complex.I • hk.conjugateFunctional ξ η := by
  change star (k ξ (C.mulI η)) = Complex.I * star (k ξ η)
  rw [hk.I_right, star_mul]
  simp only [star_neg, Complex.star_def, Complex.conj_I, neg_neg, mul_comm]

/-- The continuous scalar functional associated with a core input. -/
def extendedFunctional (ξ : C.space) : H →L[ℂ] ℂ :=
  C.extendComplex (hk.conjugateFunctional ξ) (hk.conjugateFunctional_bound ξ)
    (hk.conjugateFunctional_mulI ξ)

@[simp]
theorem extendedFunctional_coe (ξ η : C.space) :
    hk.extendedFunctional ξ (η : H) = star (k ξ η) :=
  C.extendComplex_coe _ _ _ η

variable [CompleteSpace H]

/-- Riesz representation supplies the image of a core vector. -/
def coreVector (ξ : C.space) : H :=
  (InnerProductSpace.toDual ℂ H).symm (hk.extendedFunctional ξ)

theorem coreVector_inner (ξ η : C.space) :
    inner ℂ (η : H) (hk.coreVector ξ) = k ξ η := by
  calc
    inner ℂ (η : H) (hk.coreVector ξ) =
        star (inner ℂ (hk.coreVector ξ) (η : H)) :=
      (inner_conj_symm (η : H) (hk.coreVector ξ)).symm
    _ = star (hk.extendedFunctional ξ (η : H)) := by
      rw [coreVector, InnerProductSpace.toDual_symm_apply]
    _ = k ξ η := by rw [hk.extendedFunctional_coe, star_star]

theorem coreVector_bound (ξ : C.space) :
    ‖hk.coreVector ξ‖ ≤ K.bound * ‖(ξ : H)‖ := by
  rw [coreVector, (InnerProductSpace.toDual ℂ H).symm.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg K.bound_nonneg (norm_nonneg _)
  · exact C.norm_extendComplex_le _ (hk.conjugateFunctional_bound ξ)
      (hk.conjugateFunctional_mulI ξ)

theorem coreVector_add (ξ ζ : C.space) :
    hk.coreVector (ξ + ζ) = hk.coreVector ξ + hk.coreVector ζ := by
  apply C.dense.eq_of_inner_right ℂ
  intro η hη
  let η' : C.space := ⟨η, hη⟩
  change inner ℂ (η' : H) _ = inner ℂ (η' : H) _
  rw [inner_add_right, hk.coreVector_inner, hk.coreVector_inner, hk.coreVector_inner,
    hk.add_left]

theorem coreVector_rat_smul (r : ℚ) (ξ : C.space) :
    hk.coreVector (r • ξ) = r • hk.coreVector ξ := by
  apply C.dense.eq_of_inner_right ℂ
  intro η hη
  let η' : C.space := ⟨η, hη⟩
  change inner ℂ (η' : H) _ = inner ℂ (η' : H) _
  have hs : r • hk.coreVector ξ = (r : ℂ) • hk.coreVector ξ := by
    simpa only [Rat.cast_id] using ratCast_smul_eq ℚ ℂ r (hk.coreVector ξ)
  rw [hs, inner_smul_right,
    hk.coreVector_inner, hk.coreVector_inner, hk.rat_left]

theorem coreVector_mulI (ξ : C.space) :
    hk.coreVector (C.mulI ξ) = Complex.I • hk.coreVector ξ := by
  apply C.dense.eq_of_inner_right ℂ
  intro η hη
  let η' : C.space := ⟨η, hη⟩
  change inner ℂ (η' : H) _ = inner ℂ (η' : H) _
  rw [inner_smul_right, hk.coreVector_inner, hk.coreVector_inner, hk.I_left]

/-- The Riesz images form a rational-linear map on the core. -/
def coreLinearMap : C.space →ₗ[ℚ] H where
  toFun := hk.coreVector
  map_add' := hk.coreVector_add
  map_smul' := hk.coreVector_rat_smul

theorem coreLinearMap_bound (ξ : C.space) :
    ‖hk.coreLinearMap ξ‖ ≤ K.bound * ‖(ξ : H)‖ := hk.coreVector_bound ξ

theorem coreLinearMap_mulI (ξ : C.space) :
    hk.coreLinearMap (C.mulI ξ) = Complex.I • hk.coreLinearMap ξ := hk.coreVector_mulI ξ

/-- The bounded complex-linear operator reconstructed from the kernel. -/
def toOperator : H →L[ℂ] H :=
  C.extendComplex hk.coreLinearMap hk.coreLinearMap_bound hk.coreLinearMap_mulI

theorem toOperator_norm_le : ‖hk.toOperator‖ ≤ K.bound := by
  apply ContinuousLinearMap.opNorm_le_bound _ K.bound_nonneg
  exact C.norm_extendComplex_le hk.coreLinearMap hk.coreLinearMap_bound hk.coreLinearMap_mulI

theorem toOperator_inner (ξ η : C.space) :
    inner ℂ (η : H) (hk.toOperator (ξ : H)) = k ξ η := by
  rw [toOperator, C.extendComplex_coe]
  exact hk.coreVector_inner ξ η

end ScalarOperatorKernel.CoherentCore

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialCauchySchwarz
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.traceCenter_apply _root_.OAI.KadisonKastler.traceTwoNorm_eq_zero_iff _root_.OAI.KadisonKastler.traceTwoNorm_mul_unitary _root_.OAI.KadisonKastler.traceTwoNorm_neg _root_.OAI.KadisonKastler.traceTwoNorm_unitary_mul _root_.OAI.KadisonKastler.traceTwoNorm_zero _root_.OAI.KadisonKastler.trace_traceCenter _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Cauchy–Schwarz for the faithful tracial two-norm

The imaginary-part condition on positive squares gives the Hermitian
symmetry of the trace pairing by polarization. The existing algebraic
inner-product core then supplies Cauchy–Schwarz, without changing the
ambient C*-algebra norm.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

/-- Cauchy–Schwarz for the complex trace pairing. -/
theorem FaithfulTracialState.cauchySchwarz (τ : FaithfulTracialState B) (x y : B) :
    ‖τ.toLinearMap (star x * y)‖ ≤ traceTwoNorm τ x * traceTwoNorm τ y := by
  let : PreInnerProductSpace.Core ℂ B := tracialInnerCore τ
  have hc := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) x y
  change ‖τ.toLinearMap (star x * y)‖ * ‖τ.toLinearMap (star y * x)‖ ≤
    (τ.toLinearMap (star x * x)).re * (τ.toLinearMap (star y * y)).re at hc
  have hn : ‖τ.toLinearMap (star y * x)‖ = ‖τ.toLinearMap (star x * y)‖ := by
    rw [← norm_star (τ.toLinearMap (star y * x)), τ.star_pair_symm x y]
  rw [hn] at hc
  have hs : ‖τ.toLinearMap (star x * y)‖ ^ 2 ≤
      (traceTwoNorm τ x * traceTwoNorm τ y) ^ 2 := by
    rw [mul_pow, traceTwoNorm_sq, traceTwoNorm_sq, pow_two]
    exact hc
  have hp := mul_nonneg (traceTwoNorm_nonneg τ x) (traceTwoNorm_nonneg τ y)
  nlinarith [norm_nonneg (τ.toLinearMap (star x * y))]

/-- Cauchy–Schwarz with the identity bounds a trace by the two-norm. -/
theorem FaithfulTracialState.norm_apply_le_traceTwoNorm (τ : FaithfulTracialState B) (x : B) :
    ‖τ.toLinearMap x‖ ≤ traceTwoNorm τ x := by
  simpa only [star_one, one_mul, traceTwoNorm_one] using τ.cauchySchwarz 1 x

/-- The tracial two-norm satisfies the triangle inequality. -/
theorem traceTwoNorm_add_le (τ : FaithfulTracialState B) (x y : B) :
    traceTwoNorm τ (x + y) ≤ traceTwoNorm τ x + traceTwoNorm τ y := by
  have hxy : (τ.toLinearMap (star x * y)).re ≤ traceTwoNorm τ x * traceTwoNorm τ y :=
    (Complex.re_le_norm _).trans (τ.cauchySchwarz x y)
  have hyx : (τ.toLinearMap (star y * x)).re ≤ traceTwoNorm τ x * traceTwoNorm τ y := by
    simpa only [mul_comm] using (Complex.re_le_norm _).trans (τ.cauchySchwarz y x)
  have he : (τ.toLinearMap (star (x + y) * (x + y))).re =
      (τ.toLinearMap (star x * x)).re + (τ.toLinearMap (star x * y)).re +
        (τ.toLinearMap (star y * x)).re + (τ.toLinearMap (star y * y)).re := by
    simp only [star_add, add_mul, mul_add, map_add, Complex.add_re]
    ring
  have hsum := traceTwoNorm_sq τ (x + y)
  rw [he] at hsum
  have hx := traceTwoNorm_sq τ x
  have hy := traceTwoNorm_sq τ y
  have hn := traceTwoNorm_nonneg τ (x + y)
  have hnx := traceTwoNorm_nonneg τ x
  have hny := traceTwoNorm_nonneg τ y
  nlinarith

/-- The tracial two-norm is dominated by the original operator norm. -/
theorem traceTwoNorm_le_norm (τ : FaithfulTracialState B) (x : B) :
    traceTwoNorm τ x ≤ ‖x‖ := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hpos : 0 ≤ algebraMap ℝ B (‖x‖ ^ 2) - star x * x :=
    sub_nonneg.mpr (CStarAlgebra.star_mul_le_algebraMap_norm_sq)
  obtain ⟨z, hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpos
  have hscalar : τ.toLinearMap (algebraMap ℝ B (‖x‖ ^ 2)) =
      Complex.ofReal (‖x‖ ^ 2) := by
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul, τ.map_one]
    simp
  have ht := τ.positive z
  rw [← hz, map_sub, hscalar, Complex.sub_re, Complex.ofReal_re] at ht
  have hs := traceTwoNorm_sq τ x
  have hn := traceTwoNorm_nonneg τ x
  nlinarith [norm_nonneg x]

/-- In particular, the normalized positive trace is a contraction. -/
theorem FaithfulTracialState.norm_apply_le_norm (τ : FaithfulTracialState B) (x : B) :
    ‖τ.toLinearMap x‖ ≤ ‖x‖ :=
  (τ.norm_apply_le_traceTwoNorm x).trans (traceTwoNorm_le_norm τ x)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FaithfulTraceGNS
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.traceCenter_apply _root_.OAI.KadisonKastler.traceTwoNorm_eq_zero_iff _root_.OAI.KadisonKastler.traceTwoNorm_mul_unitary _root_.OAI.KadisonKastler.traceTwoNorm_neg _root_.OAI.KadisonKastler.traceTwoNorm_unitary_mul _root_.OAI.KadisonKastler.traceTwoNorm_zero _root_.OAI.KadisonKastler.trace_traceCenter _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete GNS representation of a faithful tracial state -/

namespace KadisonKastler

open scoped ComplexOrder InnerProductSpace

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def FaithfulTracialState.toPositiveLinearMap (τ : FaithfulTracialState A) : A →ₚ[ℂ] ℂ where
  toLinearMap := τ.toLinearMap
  monotone' := by
    intro a b hab
    change τ.toLinearMap a ≤ τ.toLinearMap b
    obtain ⟨z, hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hab)
    have hp : 0 ≤ τ.toLinearMap (b - a) := by
      rw [hz]
      exact Complex.nonneg_iff.mpr ⟨τ.positive z, (τ.positive_im z).symm⟩
    rw [map_sub] at hp
    exact sub_nonneg.mp hp

abbrev TraceStateHilbert (τ : FaithfulTracialState A) := τ.toPositiveLinearMap.GNS

def traceStateVector (τ : FaithfulTracialState A) (a : A) : TraceStateHilbert τ :=
  τ.toPositiveLinearMap.toPreGNS a

def traceStateRepresentation (τ : FaithfulTracialState A) :
    A →⋆ₐ[ℂ] (TraceStateHilbert τ →L[ℂ] TraceStateHilbert τ) :=
  τ.toPositiveLinearMap.gnsStarAlgHom

theorem norm_traceStateVector (τ : FaithfulTracialState A) (a : A) :
    ‖traceStateVector τ a‖ = traceTwoNorm τ a := by
  rw [traceStateVector, UniformSpace.Completion.norm_coe, PositiveLinearMap.preGNS_norm_def]
  rfl

@[simp] theorem traceStateVector_sub (τ : FaithfulTracialState A) (a b : A) :
    traceStateVector τ (a - b) = traceStateVector τ a - traceStateVector τ b := by
  simp only [traceStateVector, map_sub, UniformSpace.Completion.coe_sub]

@[simp] theorem traceStateRepresentation_vector (τ : FaithfulTracialState A) (a b : A) :
    traceStateRepresentation τ a (traceStateVector τ b) = traceStateVector τ (a * b) := by
  change τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom a
    (τ.toPositiveLinearMap.toPreGNS b) = _
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
  rfl

theorem traceStateVector_dense (τ : FaithfulTracialState A) : DenseRange (traceStateVector τ) := by
  apply UniformSpace.Completion.denseRange_coe.mono
  rintro _ ⟨a, rfl⟩
  exact ⟨τ.toPositiveLinearMap.ofPreGNS a, rfl⟩

theorem traceStateRepresentation_injective (τ : FaithfulTracialState A) :
    Function.Injective (traceStateRepresentation τ) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have hz : traceStateVector τ a = 0 := by
    have h := congrArg (fun T => T (traceStateVector τ 1)) ha
    simpa only [traceStateRepresentation_vector, mul_one,
      zero_apply] using h
  apply τ.faithful
  have hn : traceTwoNorm τ a = 0 := by rw [← norm_traceStateVector, hz, norm_zero]
  apply Complex.ext
  · have hs := traceTwoNorm_sq τ a
    rw [hn, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
    exact hs.symm
  · exact τ.positive_im a

theorem norm_traceStateRepresentation (τ : FaithfulTracialState A) (a : A) :
    ‖traceStateRepresentation τ a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (traceStateRepresentation τ).toNonUnitalStarAlgHom
    (traceStateRepresentation_injective τ) a

/-- Right multiplication, supplied by the same tracial GNS construction. -/
def traceStateRight (τ : FaithfulTracialState A) (a : A) :
    TraceStateHilbert τ →L[ℂ] TraceStateHilbert τ :=
  NuclearTrace.rightGNS τ.toPositiveLinearMap τ.tracial (MulOpposite.op a)

@[simp] theorem traceStateRight_vector (τ : FaithfulTracialState A) (a b : A) :
    traceStateRight τ a (traceStateVector τ b) = traceStateVector τ (b * a) := by
  exact NuclearTrace.rightGNS_coe τ.toPositiveLinearMap τ.tracial (MulOpposite.op a)
    (τ.toPositiveLinearMap.toPreGNS b)

theorem traceState_left_right_commute (τ : FaithfulTracialState A) (a b : A) :
    Commute (traceStateRepresentation τ a) (traceStateRight τ b) :=
  NuclearTrace.left_right_commute τ.toPositiveLinearMap τ.tracial a (MulOpposite.op b)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InvariantOperatorMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Operator averaging from an actual scalar invariant mean

The scalar mean is data on bounded scalar functions. Riesz representation
constructs the operator average from its coefficients. No operator-valued
mean, fixed-point projection, or amenability conclusion is assumed.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction BigOperators Topology CStarAlgebra

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

namespace ScalarInvariantMean

variable (m : ScalarInvariantMean G)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Group G] [CompleteSpace H] in
theorem coefficient_smul_input (F : G →ᵇ (H →L[ℂ] H)) (c : ℂ) (x y : H) :
    coefficient F (c • x) y = c • coefficient F x y := by
  ext g
  simp only [coefficient_apply, BoundedContinuousFunction.smul_apply, map_smul,
    inner_smul_right, smul_eq_mul]

theorem inner_operatorValue (F : G →ᵇ (H →L[ℂ] H)) (x y : H) :
    inner ℂ y (m.operatorValue F x) = m.toCLM (coefficient F x y) := by
  calc
    inner ℂ y (m.operatorValue F x) = star (inner ℂ (m.operatorValue F x) y) :=
      (inner_conj_symm y (m.operatorValue F x)).symm
    _ = star (m.testFunctional F x y) := by
      rw [operatorValue, InnerProductSpace.toDual_symm_apply]
    _ = _ := star_star _

theorem norm_operatorValue_le (F : G →ᵇ (H →L[ℂ] H)) (x : H) :
    ‖m.operatorValue F x‖ ≤ ‖F‖ * ‖x‖ := by
  rw [operatorValue, (InnerProductSpace.toDual ℂ H).symm.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  change ‖star (m.toCLM (coefficient F x y))‖ ≤ _
  rw [norm_star]
  exact (m.norm_le _).trans (norm_coefficient_le F x y)

def operator (F : G →ᵇ (H →L[ℂ] H)) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := m.operatorValue F
      map_add' := fun x z => by
        apply ext_inner_left ℂ
        intro y
        rw [inner_add_right, m.inner_operatorValue, m.inner_operatorValue,
          m.inner_operatorValue, coefficient_add_input, map_add]
      map_smul' := fun c x => by
        apply ext_inner_left ℂ
        intro y
        rw [inner_smul_right, m.inner_operatorValue, m.inner_operatorValue,
          coefficient_smul_input, map_smul]
        rfl }
    ‖F‖ (m.norm_operatorValue_le F)

@[simp] theorem inner_operator (F : G →ᵇ (H →L[ℂ] H)) (x y : H) :
    inner ℂ y (m.operator F x) = m.toCLM (coefficient F x y) :=
  m.inner_operatorValue F x y

theorem norm_operator_le (F : G →ᵇ (H →L[ℂ] H)) : ‖m.operator F‖ ≤ ‖F‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F) (m.norm_operatorValue_le F)

theorem operator_add (F J : G →ᵇ (H →L[ℂ] H)) :
    m.operator (F + J) = m.operator F + m.operator J := by
  ext x
  apply ext_inner_left ℂ
  intro y
  simp only [add_apply, inner_add_right, m.inner_operator]
  rw [← map_add]
  congr 1
  ext g
  simp only [coefficient_apply, BoundedContinuousFunction.add_apply, add_apply, inner_add_right]

theorem operator_smul (c : ℂ) (F : G →ᵇ (H →L[ℂ] H)) :
    m.operator (c • F) = c • m.operator F := by
  ext x
  apply ext_inner_left ℂ
  intro y
  simp only [smul_apply, inner_smul_right, m.inner_operator]
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  ext g
  simp only [coefficient_apply, BoundedContinuousFunction.smul_apply,
    smul_apply, inner_smul_right, smul_eq_mul]

/-- The actual contractive complex-linear operator average. -/
def operatorMean : (G →ᵇ (H →L[ℂ] H)) →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := m.operator
      map_add' := m.operator_add
      map_smul' := m.operator_smul }
    1 (fun F => by
      change ‖m.operator F‖ ≤ 1 * ‖F‖
      simpa only [one_mul] using m.norm_operator_le F)

theorem inner_operatorMean (F : G →ᵇ (H →L[ℂ] H)) (x y : H) :
    inner ℂ y (m.operatorMean F x) = m.toCLM (coefficient F x y) := m.inner_operator F x y

theorem operatorMean_left (T : H →L[ℂ] H) (F : G →ᵇ (H →L[ℂ] H)) :
    m.operatorMean (BoundedContinuousFunction.const G T * F) = T * m.operatorMean F := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [m.inner_operatorMean]
  have hc : coefficient (BoundedContinuousFunction.const G T * F) x y =
      coefficient F x (star T y) := by
    ext g
    simp only [coefficient_apply, BoundedContinuousFunction.mul_apply,
      BoundedContinuousFunction.const_apply, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  rw [hc, ← m.inner_operatorMean, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

theorem operatorMean_right (T : H →L[ℂ] H) (F : G →ᵇ (H →L[ℂ] H)) :
    m.operatorMean (F * BoundedContinuousFunction.const G T) = m.operatorMean F * T := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [m.inner_operatorMean, mul_apply_eq_comp, m.inner_operatorMean]
  congr 1

/-- Averaging an actual family in a von Neumann algebra stays in that algebra. -/
theorem operatorMean_mem (M : VonNeumannAlgebra H) (F : G →ᵇ (H →L[ℂ] H))
    (hF : ∀ g, F g ∈ M) : m.operatorMean F ∈ M := by
  change m.operatorMean F ∈ (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  intro T hT
  rw [← m.operatorMean_left, ← m.operatorMean_right]
  congr 1
  apply BoundedContinuousFunction.ext
  intro g
  exact (hT (F g) (hF g)).symm

end ScalarInvariantMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialProducts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Multiplication estimates for the tracial two-norm -/

namespace KadisonKastler

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

/-- Left multiplication costs at most the ambient operator norm. -/
theorem traceTwoNorm_mul_le_left (τ : FaithfulTracialState B) (x y : B) :
    traceTwoNorm τ (x * y) ≤ ‖x‖ * traceTwoNorm τ y := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hpos : 0 ≤ algebraMap ℝ B (‖x‖ ^ 2) - star x * x :=
    sub_nonneg.mpr (CStarAlgebra.star_mul_le_algebraMap_norm_sq)
  obtain ⟨z, hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpos
  have he : star (z * y) * (z * y) =
      (‖x‖ ^ 2 : ℂ) • (star y * y) - star (x * y) * (x * y) := by
    calc
      star (z * y) * (z * y) = star y * (star z * z) * y := by
        simp only [star_mul, mul_assoc]
      _ = star y * (algebraMap ℝ B (‖x‖ ^ 2) - star x * x) * y := by rw [hz]
      _ = (‖x‖ ^ 2 : ℂ) • (star y * y) - star (x * y) * (x * y) := by
        rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
        simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one,
          star_mul, mul_assoc]
        norm_cast
  have ht := τ.positive (z * y)
  rw [he, map_sub, map_smul, smul_eq_mul, Complex.sub_re] at ht
  have hr : ((‖x‖ ^ 2 : ℂ) * τ.toLinearMap (star y * y)).re =
      ‖x‖ ^ 2 * (τ.toLinearMap (star y * y)).re := by
    rw [← Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hr] at ht
  have hxy := traceTwoNorm_sq τ (x * y)
  have hy := traceTwoNorm_sq τ y
  have hn := mul_nonneg (norm_nonneg x) (traceTwoNorm_nonneg τ y)
  have hs : traceTwoNorm τ (x * y) ^ 2 ≤ (‖x‖ * traceTwoNorm τ y) ^ 2 := by
    rw [mul_pow, hxy, hy]
    linarith
  nlinarith [traceTwoNorm_nonneg τ (x * y)]

/-- Right multiplication has the corresponding operator-norm bound. -/
theorem traceTwoNorm_mul_le_right (τ : FaithfulTracialState B) (x y : B) :
    traceTwoNorm τ (x * y) ≤ traceTwoNorm τ x * ‖y‖ := by
  calc
    traceTwoNorm τ (x * y) = traceTwoNorm τ (star y * star x) := by
      rw [← star_mul, traceTwoNorm_star]
    _ ≤ ‖star y‖ * traceTwoNorm τ (star x) := traceTwoNorm_mul_le_left τ _ _
    _ = traceTwoNorm τ x * ‖y‖ := by rw [norm_star, traceTwoNorm_star, mul_comm]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VaryingSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded products for the finite-matrix model

The matrix sizes in the preliminary free model vary with the coordinate.
The existing `lp` space at infinity supplies its ordinary bounded-product
C*-algebra, without identifying the operator norm with a tracial norm.
-/

namespace KadisonKastler

noncomputable section

universe u v

variable (B : ℕ → Type u) [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]

instance varyingSequenceCStarAlgebra : CStarAlgebra (VaryingBoundedSequence B) where
  __ := lp.inftyNormedRing (B := B)
  __ := lp.inftyStarRing (B := B)
  __ := lp.inftyCStarRing (B := B)
  __ := lp.inftyNormedAlgebra (𝕜 := ℂ) (B := B)
  __ := (inferInstance : CompleteSpace (lp B (⊤ : ENNReal)))
  __ := (inferInstance : StarModule ℂ (lp B (⊤ : ENNReal)))

variable {B}

omit [∀ j, Nontrivial (B j)] in
theorem varyingSequence_norm_apply_le (x : VaryingBoundedSequence B) (j : ℕ) :
    ‖x j‖ ≤ ‖x‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero x j

variable {C : Type v} [CStarAlgebra C]

/-- Coordinate star embeddings into a fixed factor induce the map on
bounded products used for the finite-matrix model. -/
def varyingSequenceMap (φ : ∀ j, B j →⋆ₐ[ℂ] C) :
    VaryingBoundedSequence B →⋆ₐ[ℂ] BoundedSequence C where
  toFun x := BoundedContinuousFunction.mkOfDiscrete (fun j => φ j (x j)) (2 * ‖x‖) (by
    intro i j
    calc
      dist (φ i (x i)) (φ j (x j)) ≤ ‖φ i (x i)‖ + ‖φ j (x j)‖ := dist_le_norm_add_norm _ _
      _ ≤ ‖x i‖ + ‖x j‖ := add_le_add (NonUnitalStarAlgHom.norm_apply_le (φ i) _)
        (NonUnitalStarAlgHom.norm_apply_le (φ j) _)
      _ ≤ 2 * ‖x‖ := by linarith [varyingSequence_norm_apply_le x i, varyingSequence_norm_apply_le x j])
  map_one' := by apply BoundedContinuousFunction.ext; intro j; exact map_one (φ j)
  map_mul' x y := by apply BoundedContinuousFunction.ext; intro j; exact map_mul (φ j) (x j) (y j)
  map_zero' := by apply BoundedContinuousFunction.ext; intro j; exact map_zero (φ j)
  map_add' x y := by apply BoundedContinuousFunction.ext; intro j; exact map_add (φ j) (x j) (y j)
  commutes' c := by apply BoundedContinuousFunction.ext; intro j; exact (φ j).commutes c
  map_star' x := by apply BoundedContinuousFunction.ext; intro j; exact map_star (φ j) (x j)

@[simp]
theorem varyingSequenceMap_apply (φ : ∀ j, B j →⋆ₐ[ℂ] C)
    (x : VaryingBoundedSequence B) (j : ℕ) : varyingSequenceMap φ x j = φ j (x j) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakOperatorCoefficients
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.BoundedHochschild.WeakSubspace.preannihilator_closed_instance _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCStarQuotient.starSubalgebra_closed _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.corner_closed _root_.OAI.HochschildMatrixSystems.MatrixSystem.commutant_closed _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cstarCornerSubalgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerClosed _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.PopaCorner.algebra_closed _root_.OAI.PopaCorner.instNormedRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar coefficients determine weak operator fields -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

/-- A representative is the one-element case of a uniformly bounded family. -/
def asUniformFamily (F : WeakOperatorRepresentative (H := H) μ) :
    UniformMeasurableOperators Unit D H μ where
  eval _ := eval F
  bound := ‖F‖
  bound_nonneg := norm_nonneg F
  norm_le _ := eval_norm_le F
  measurable _ := eval_aestronglyMeasurable F

/-- Scalar matrix coefficients as L-infinity classes. -/
def coefficient (F : WeakOperatorRepresentative (H := H) μ) (ξ η : H) : ScalarLInfinity μ :=
  (asUniformFamily F).coefficient () ξ η

omit [IsFiniteMeasure μ] in
theorem coefficient_ae (F : WeakOperatorRepresentative (H := H) μ) (ξ η : H) :
    coefficient F ξ η =ᵐ[μ] fun x => inner ℂ η (eval F x ξ) :=
  (asUniformFamily F).coefficient_ae () ξ η

/-- The bounded sesquilinear kernel of a representative. -/
def scalarKernel (F : WeakOperatorRepresentative (H := H) μ) : ScalarOperatorKernel H μ where
  coeff := coefficient F
  bound := ‖F‖
  bound_nonneg := norm_nonneg F
  norm_le := (asUniformFamily F).norm_coefficient_le ()
  add_left := (asUniformFamily F).coefficient_add_left ()
  add_right := (asUniformFamily F).coefficient_add_right ()
  smul_left := (asUniformFamily F).coefficient_smul_left ()
  smul_right := (asUniformFamily F).coefficient_smul_right ()

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_KernelReconstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reconstructing measurable operator fields from scalar kernels

The coherent countable-core representatives give pointwise bounded
operators. Dense scalar tests prove measurability; continuity of the
L-infinity kernel then identifies all coefficients.
-/

namespace KadisonKastler

open MeasureTheory Filter TopologicalSpace

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ScalarOperatorKernel

variable (K : ScalarOperatorKernel H μ) (C : RationalComplexCore H)

/-- The scalar kernel gives a bounded operator at every good point,
and zero on the exceptional null set. -/
def reconstructedOperator (x : D) : H →L[ℂ] H := by
  classical
  exact if h : K.CoherentCore C (fun ξ η => K.coeff (ξ : H) (η : H) x) then h.toOperator else 0

theorem reconstructedOperator_norm_le (x : D) : ‖K.reconstructedOperator C x‖ ≤ K.bound := by
  unfold reconstructedOperator
  split_ifs with h
  · exact h.toOperator_norm_le
  · simpa only [norm_zero] using K.bound_nonneg

/-- Every countable-core matrix coefficient is the supplied scalar representative. -/
theorem reconstructedOperator_core_ae (ξ η : C.space) :
    ∀ᵐ x ∂μ, inner ℂ (η : H) (K.reconstructedOperator C x (ξ : H)) = K.coeff ξ η x := by
  filter_upwards [K.coherentCore_ae C] with x hx
  simpa only [reconstructedOperator, dite_eq_left hx] using hx.toOperator_inner ξ η

end ScalarOperatorKernel

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OrthonormalMatrixUnits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Full matrix units from a finite orthonormal basis -/

open scoped BigOperators

noncomputable section

namespace Generator

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι]

/-- The rank-one matrix units associated with an orthonormal basis. -/
def orthonormalMatrixUnits (b : OrthonormalBasis ι ℂ H) : MatrixUnitSystem ι (H →L[ℂ] H) where
  entry i j := InnerProductSpace.rankOne ℂ (b i) (b j)
  star_entry i j := by
    rw [ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]
  mul_entry i j k l := by
    change (InnerProductSpace.rankOne ℂ (b i) (b j)).comp
      (InnerProductSpace.rankOne ℂ (b k) (b l)) = _
    rw [InnerProductSpace.rankOne_comp_rankOne, b.inner_eq_ite]
    split_ifs <;> simp_all
  total := b.sum_rankOne_eq_id

@[simp]
theorem orthonormalMatrixUnits_entry_apply (b : OrthonormalBasis ι ℂ H)
    (i j : ι) (x : H) :
    (orthonormalMatrixUnits b).entry i j x = inner ℂ (b j) x • b i := rfl

/-- These matrix units span all bounded operators on the finite Hilbert space. -/
theorem orthonormalMatrixUnits_surjective (b : OrthonormalBasis ι ℂ H) :
    Function.Surjective (orthonormalMatrixUnits b).hom := by
  intro T
  let a : Matrix ι ι ℂ := fun i j => inner ℂ (b i) (T (b j))
  refine ⟨a, ?_⟩
  have hb (j : ι) : (orthonormalMatrixUnits b).hom a (b j) = T (b j) := by
    calc
      _ = ∑ i, inner ℂ (b i) (T (b j)) • b i := by
        change (∑ i, ∑ k, a i k • InnerProductSpace.rankOne ℂ (b i) (b k)) (b j) = _
        simp only [sum_apply, smul_apply, InnerProductSpace.rankOne_apply,
          b.inner_eq_ite, smul_smul]
        simp [a, mul_ite, ite_smul]
      _ = _ := b.sum_repr' _
  apply ContinuousLinearMap.ext
  intro x
  rw [← b.sum_repr' x]
  simp only [map_sum, map_smul, hb]

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreMatrixData
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable equivalent projection families give full matrix corners

The input here is actual projection and partial-isometry data in a represented
von Neumann algebra.  No existence of a semifinite decomposition is assumed as
a published input.  Once such a decomposition has been constructed, the
matrix-corner machinery applies to the explicit operators `v i * star (v j)`.
-/

namespace KadisonKastler

open Generator.Tracial
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- Orthogonality of the final projections forces the cross-products of the
partial isometries to vanish. -/
theorem projectionFamily_cross_eq_zero
    (p : ℕ → AlgebraProjection M) (v : ℕ → Algebra M)
    (hvi : ∀ i, star (v i) * v i = (p 0).val)
    (hvf : ∀ i, v i * star (v i) = (p i).val)
    (horth : Pairwise (fun i j => (p i).val * (p j).val = 0))
    {i j : ℕ} (hij : i ≠ j) : star (v i) * v j = 0 := by
  let V (k : ℕ) : PartialIsometry M := ⟨p 0, v k, hvi k⟩
  have ht (k : ℕ) : (V k).target = p k := Subtype.ext (hvf k)
  exact (V i).adjoint.mul_eq_zero (V j) (by
    change (V i).target.val * (V j).target.val = 0
    rw [ht, ht]
    exact horth hij)

theorem projectionFamilyEntry_mul
    (p : ℕ → AlgebraProjection M) (v : ℕ → Algebra M)
    (hvi : ∀ i, star (v i) * v i = (p 0).val)
    (hvf : ∀ i, v i * star (v i) = (p i).val)
    (horth : Pairwise (fun i j => (p i).val * (p j).val = 0))
    (i j k l : ℕ) :
    projectionFamilyEntry v i j * projectionFamilyEntry v k l =
      if j = k then projectionFamilyEntry v i l else 0 := by
  classical
  let V (a : ℕ) : PartialIsometry M := ⟨p 0, v a, hvi a⟩
  by_cases hjk : j = k
  · subst k
    rw [ite_eq_left rfl]
    change (v i * star (v j)) * (v j * star (v l)) = v i * star (v l)
    calc
      _ = (v i * (star (v j) * v j)) * star (v l) := by
        simp only [mul_assoc]
      _ = v i * star (v l) := by
        rw [hvi, show v i * (p 0).val = v i from (V i).mul_support]
  · rw [ite_eq_right hjk]
    change (v i * star (v j)) * (v k * star (v l)) = 0
    calc
      _ = (v i * (star (v j) * v k)) * star (v l) := by
        simp only [mul_assoc]
      _ = 0 := by
        rw [projectionFamily_cross_eq_zero p v hvi hvf horth hjk, mul_zero, zero_mul]

namespace FullMatrixCorner

/-- A countable strong partition into equivalent projections supplies actual
full matrix units with the prescribed initial Hilbert corner. -/
def ofEquivalentProjectionFamily
    (E : Submodule ℂ H) [CompleteSpace E]
    (p : ℕ → AlgebraProjection M) (v : ℕ → Algebra M)
    (hvi : ∀ i, star (v i) * v i = (p 0).val)
    (hvf : ∀ i, v i * star (v i) = (p i).val)
    (horth : Pairwise (fun i j => (p i).val * (p j).val = 0))
    (hp0 : ((p 0).val : H →L[ℂ] H) = E.starProjection)
    (htotal : ∀ x : H, HasSum (fun i => ((p i).val : H →L[ℂ] H) x) x) :
    FullMatrixCorner E where
  entry i j := projectionFamilyEntry v i j
  star_entry i j := congrArg Subtype.val (projectionFamilyEntry_star v i j)
  mul_entry i j k l := by
    classical
    have h := congrArg Subtype.val (projectionFamilyEntry_mul p v hvi hvf horth i j k l)
    by_cases hjk : j = k
    · simpa only [ite_eq_left hjk, MulMemClass.coe_mul] using h
    · simpa only [ite_eq_right hjk, MulMemClass.coe_mul, ZeroMemClass.coe_zero] using h
  zero_zero := (congrArg Subtype.val (hvf 0)).trans hp0
  total x := by
    simpa only [projectionFamilyEntry, hvf] using htotal x

@[simp] theorem ofEquivalentProjectionFamily_entry
    (E : Submodule ℂ H) [CompleteSpace E]
    (p : ℕ → AlgebraProjection M) (v : ℕ → Algebra M)
    (hvi : ∀ i, star (v i) * v i = (p 0).val)
    (hvf : ∀ i, v i * star (v i) = (p i).val)
    (horth : Pairwise (fun i j => (p i).val * (p j).val = 0))
    (hp0 : ((p 0).val : H →L[ℂ] H) = E.starProjection)
    (htotal : ∀ x : H, HasSum (fun i => ((p i).val : H →L[ℂ] H) x) x)
    (i j : ℕ) :
    (ofEquivalentProjectionFamily E p v hvi hvf horth hp0 htotal).entry i j =
      ((v i * star (v j) : Algebra M) : H →L[ℂ] H) := rfl

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SubalgebraInvariantMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.conjugateLinear_one _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe _root_.OAI.UltrapowerBridge.quotientMap_smul _root_.OAI.UltrapowerBridge.quotientMap_star _root_.OAI.UltrapowerBridge.quotientTrace_mk _root_.OAI.UltrapowerBridge.quotientTrace_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Restricting an invariant operator mean to a von Neumann algebra

The coefficient construction preserves every von Neumann algebra. Restricting
its domain and codomain therefore gives the exact mean for internal unitary
correction, without a normality or injectivity assumption on the target.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance subalgebraFamilyCStar_rab37e7_1 (N : VonNeumannAlgebra H) :
    CStarAlgebra (G →ᵇ Algebra N) where
/-- Pointwise inclusion of bounded algebra-valued families. -/
def ambientAlgebraFamily (N : VonNeumannAlgebra H) :
    (G →ᵇ Algebra N) →⋆ₐ[ℂ] (G →ᵇ (H →L[ℂ] H)) where
  toFun F := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => (F g : H →L[ℂ] H)) ‖F‖ (fun g => F.norm_coe_le_norm g)
  map_one' := by ext g; rfl
  map_mul' _ _ := by ext g; rfl
  map_zero' := by ext g; rfl
  map_add' _ _ := by ext g; rfl
  commutes' _ := by ext g; rfl
  map_star' _ := by ext g; rfl

omit [Group G] in
@[simp]
theorem ambientAlgebraFamily_apply (N : VonNeumannAlgebra H)
    (F : G →ᵇ Algebra N) (g : G) : ambientAlgebraFamily N F g = (F g : H →L[ℂ] H) := rfl

omit [Group G] in
theorem norm_ambientAlgebraFamily_le (N : VonNeumannAlgebra H) (F : G →ᵇ Algebra N) :
    ‖ambientAlgebraFamily N F‖ ≤ ‖F‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr (fun g => F.norm_coe_le_norm g)

namespace ScalarInvariantMean

variable (m : ScalarInvariantMean G) (N : VonNeumannAlgebra H)

local instance subalgebraFamilyCStar_rab37e7_2 (N : VonNeumannAlgebra H) :
    CStarAlgebra (G →ᵇ Algebra N) where
/-- The actual algebra-valued mean. -/
def algebraMean : (G →ᵇ Algebra N) →L[ℂ] Algebra N :=
  LinearMap.mkContinuous
    { toFun F := ⟨m.operatorMean (ambientAlgebraFamily N F),
        m.operatorMean_mem N _ (fun g => (F g).property)⟩
      map_add' F J := by
        apply Subtype.ext
        simp only [map_add, AddMemClass.coe_add]
      map_smul' c F := by
        apply Subtype.ext
        change m.operatorMean (ambientAlgebraFamily N (c • F)) =
          c • m.operatorMean (ambientAlgebraFamily N F)
        have h : ambientAlgebraFamily N (c • F) = c • ambientAlgebraFamily N F :=
          (ambientAlgebraFamily N).toAlgHom.toLinearMap.map_smul c F
        rw [h, map_smul] }
    1 (fun F => by
      change ‖m.operator (ambientAlgebraFamily N F)‖ ≤ 1 * ‖F‖
      rw [one_mul]
      exact (m.norm_operator_le _).trans (norm_ambientAlgebraFamily_le N F))

@[simp]
theorem algebraMean_coe (F : G →ᵇ Algebra N) :
    (m.algebraMean N F : H →L[ℂ] H) = m.operatorMean (ambientAlgebraFamily N F) := rfl

end ScalarInvariantMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialSequenceState
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.traceCenter_apply _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.traceTwoNorm_eq_zero_iff _root_.OAI.KadisonKastler.traceTwoNorm_neg _root_.OAI.KadisonKastler.traceTwoNorm_zero _root_.OAI.KadisonKastler.trace_traceCenter _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The canonical trace on a bounded product

The trace is the scalar ultralimit of the coordinate traces. The varying
family covers both the constant-factor and finite-matrix products used here.
-/

namespace KadisonKastler

open Filter Set
open scoped Topology

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)]
  (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ)

theorem exists_tracialSequenceValue (x : VaryingBoundedSequence B) :
    ∃ z : ℂ, ‖z‖ ≤ ‖x‖ ∧ Tendsto (fun j => (τ j).toLinearMap (x j))
      (ω : Filter ℕ) (𝓝 z) := by
  obtain ⟨z, hz, ht⟩ := (isCompact_closedBall (0 : ℂ) ‖x‖).ultrafilter_le_nhds
    (ω.map (fun j => (τ j).toLinearMap (x j))) (by
      apply le_principal_iff.mpr
      change ∀ᶠ j in (ω : Filter ℕ), (τ j).toLinearMap (x j) ∈ Metric.closedBall (0 : ℂ) ‖x‖
      exact Eventually.of_forall (fun j => by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          ((τ j).norm_apply_le_norm (x j)).trans (varyingSequence_norm_apply_le x j)))
  exact ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz, ht⟩

def tracialSequenceValue (x : VaryingBoundedSequence B) : ℂ :=
  Classical.choose (exists_tracialSequenceValue τ ω x)

theorem norm_tracialSequenceValue (x : VaryingBoundedSequence B) :
    ‖tracialSequenceValue τ ω x‖ ≤ ‖x‖ :=
  (Classical.choose_spec (exists_tracialSequenceValue τ ω x)).1

theorem tendsto_tracialSequenceValue (x : VaryingBoundedSequence B) :
    Tendsto (fun j => (τ j).toLinearMap (x j)) (ω : Filter ℕ)
      (𝓝 (tracialSequenceValue τ ω x)) :=
  (Classical.choose_spec (exists_tracialSequenceValue τ ω x)).2

def tracialSequenceLinear : VaryingBoundedSequence B →ₗ[ℂ] ℂ where
  toFun := tracialSequenceValue τ ω
  map_add' x y := by
    apply tendsto_nhds_unique (tendsto_tracialSequenceValue τ ω (x + y))
    simpa only [lp.coeFn_add, Pi.add_apply, map_add] using
      (tendsto_tracialSequenceValue τ ω x).add (tendsto_tracialSequenceValue τ ω y)
  map_smul' c x := by
    apply tendsto_nhds_unique (tendsto_tracialSequenceValue τ ω (c • x))
    simpa only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply] using
      (tendsto_tracialSequenceValue τ ω x).const_smul c

def tracialSequenceContinuous : VaryingBoundedSequence B →L[ℂ] ℂ :=
  (tracialSequenceLinear τ ω).mkContinuous 1 (fun x => by
    change ‖tracialSequenceValue τ ω x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using norm_tracialSequenceValue τ ω x)

@[simp] theorem tracialSequenceContinuous_apply (x : VaryingBoundedSequence B) :
    tracialSequenceContinuous τ ω x = tracialSequenceValue τ ω x := rfl

variable [∀ j, Nontrivial (B j)]

@[simp] theorem tracialSequenceValue_one : tracialSequenceValue τ ω 1 = 1 := by
  apply tendsto_nhds_unique (tendsto_tracialSequenceValue τ ω 1)
  simpa only [lp.infty_coeFn_one, Pi.one_apply, FaithfulTracialState.map_one] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) (ω : Filter ℕ) (𝓝 1))

omit [∀ j, Nontrivial (B j)] in
theorem tracialSequenceValue_tracial (x y : VaryingBoundedSequence B) :
    tracialSequenceValue τ ω (x * y) = tracialSequenceValue τ ω (y * x) := by
  apply tendsto_nhds_unique (tendsto_tracialSequenceValue τ ω (x * y))
  simpa only [lp.infty_coeFn_mul, Pi.mul_apply, FaithfulTracialState.tracial] using
    tendsto_tracialSequenceValue τ ω (y * x)

omit [∀ j, Nontrivial (B j)] in
theorem tracialSequenceValue_positive (x : VaryingBoundedSequence B) :
    0 ≤ (tracialSequenceValue τ ω (star x * x)).re := by
  apply ge_of_tendsto ((Complex.continuous_re.tendsto _).comp
    (tendsto_tracialSequenceValue τ ω (star x * x)))
  exact Eventually.of_forall (fun j => (τ j).positive (x j))

omit [∀ j, Nontrivial (B j)] in
theorem tracialSequenceValue_positive_im (x : VaryingBoundedSequence B) :
    (tracialSequenceValue τ ω (star x * x)).im = 0 := by
  apply tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp
    (tendsto_tracialSequenceValue τ ω (star x * x)))
  simpa only [Function.comp_def, lp.infty_coeFn_mul, lp.coeFn_star, Pi.mul_apply,
    Pi.star_apply, FaithfulTracialState.positive_im] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) (ω : Filter ℕ) (𝓝 0))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialSequenceIdeal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The closed two-norm null ideal of a tracial bounded product -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ)

def TraceNullSequence (x : VaryingBoundedSequence B) : Prop :=
  Tendsto (fun j => traceTwoNorm (τ j) (x j)) (ω : Filter ℕ) (𝓝 0)

omit [∀ j, Nontrivial (B j)] in
theorem traceNullSequence_add {x y : VaryingBoundedSequence B}
    (hx : TraceNullSequence τ ω x) (hy : TraceNullSequence τ ω y) :
    TraceNullSequence τ ω (x + y) := by
  apply squeeze_zero (fun j => traceTwoNorm_nonneg (τ j) _)
    (fun j => traceTwoNorm_add_le (τ j) (x j) (y j))
  simpa only [add_zero] using hx.add hy

omit [∀ j, Nontrivial (B j)] in
theorem traceNullSequence_mul_left (x : VaryingBoundedSequence B)
    {y : VaryingBoundedSequence B} (hy : TraceNullSequence τ ω y) :
    TraceNullSequence τ ω (x * y) := by
  apply squeeze_zero (fun j => traceTwoNorm_nonneg (τ j) _)
    (fun j => (traceTwoNorm_mul_le_left (τ j) (x j) (y j)).trans
      (mul_le_mul_of_nonneg_right (varyingSequence_norm_apply_le x j)
        (traceTwoNorm_nonneg (τ j) _)))
  simpa only [mul_zero] using hy.const_mul ‖x‖

omit [∀ j, Nontrivial (B j)] in
theorem traceNullSequence_mul_right {x : VaryingBoundedSequence B}
    (hx : TraceNullSequence τ ω x) (y : VaryingBoundedSequence B) :
    TraceNullSequence τ ω (x * y) := by
  apply squeeze_zero (fun j => traceTwoNorm_nonneg (τ j) _)
    (fun j => (traceTwoNorm_mul_le_right (τ j) (x j) (y j)).trans
      (mul_le_mul_of_nonneg_left (varyingSequence_norm_apply_le y j)
        (traceTwoNorm_nonneg (τ j) _)))
  simpa only [zero_mul] using hx.mul_const ‖y‖

theorem isClosed_traceNullSequence :
    IsClosed {x : VaryingBoundedSequence B | TraceNullSequence τ ω x} := by
  apply isClosed_of_closure_subset
  intro x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (half_pos hε)
  have hnorm : ‖x - y‖ < ε / 2 := by simpa only [dist_eq_norm] using hxy
  filter_upwards [(Metric.tendsto_nhds.mp hy) (ε / 2) (half_pos hε)] with j hj
  have hyj : traceTwoNorm (τ j) (y j) < ε / 2 := by
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (traceTwoNorm_nonneg _ _)] using hj
  have ht : traceTwoNorm (τ j) (x j) ≤ ‖x - y‖ + traceTwoNorm (τ j) (y j) := by
    calc
      _ = traceTwoNorm (τ j) ((x j - y j) + y j) := by rw [sub_add_cancel]
      _ ≤ traceTwoNorm (τ j) (x j - y j) + traceTwoNorm (τ j) (y j) :=
        traceTwoNorm_add_le _ _ _
      _ ≤ ‖x - y‖ + traceTwoNorm (τ j) (y j) :=
        add_le_add ((traceTwoNorm_le_norm (τ j) (x j - y j)).trans
          (varyingSequence_norm_apply_le (x - y) j)) le_rfl
  simpa only [dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (traceTwoNorm_nonneg _ _)] using ht.trans_lt (by linarith)

def traceNullClosedIdeal : CuntzPureness.ClosedStarIdeal (VaryingBoundedSequence B) where
  ideal := TwoSidedIdeal.mk' {x | TraceNullSequence τ ω x}
    (by
      change Tendsto (fun j => traceTwoNorm (τ j) 0) (ω : Filter ℕ) (𝓝 0)
      simpa only [traceTwoNorm, star_zero, zero_mul, map_zero, Complex.zero_re, Real.sqrt_zero]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) (ω : Filter ℕ) (𝓝 0)))
    (traceNullSequence_add τ ω)
    (by
      intro x hx
      change TraceNullSequence τ ω (-x)
      change TraceNullSequence τ ω x at hx
      simpa only [TraceNullSequence, lp.coeFn_neg, Pi.neg_apply, traceTwoNorm,
        star_neg, neg_mul_neg] using hx)
    (by intro x y hy; exact traceNullSequence_mul_left τ ω x hy)
    (by intro x y hx; exact traceNullSequence_mul_right τ ω hx y)
  star_mem := by
    intro x hx
    change TraceNullSequence τ ω (star x - 0)
    change TraceNullSequence τ ω (x - 0) at hx
    simpa only [sub_zero, TraceNullSequence, lp.coeFn_star, Pi.star_apply, traceTwoNorm_star] using hx
  isClosed := by
    simpa only [TwoSidedIdeal.coe_mk'] using isClosed_traceNullSequence τ ω

omit [∀ j, Nontrivial (B j)] in
/-- The canonical trace vanishes on the two-norm null ideal. -/
theorem tracialSequenceValue_eq_zero_of_null {x : VaryingBoundedSequence B}
    (hx : TraceNullSequence τ ω x) : tracialSequenceValue τ ω x = 0 := by
  have hlim : Tendsto (fun j => (τ j).toLinearMap (x j)) (ω : Filter ℕ) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun j => norm_nonneg _)
      (fun j => (τ j).norm_apply_le_traceTwoNorm (x j)) hx
  exact tendsto_nhds_unique (tendsto_tracialSequenceValue τ ω x) hlim

omit [∀ j, Nontrivial (B j)] in
/-- A square has zero limit trace precisely when its sequence is two-null. -/
theorem tracialSequenceValue_square_eq_zero_iff (x : VaryingBoundedSequence B) :
    tracialSequenceValue τ ω (star x * x) = 0 ↔ TraceNullSequence τ ω x := by
  constructor
  · intro hx
    have hlim := tendsto_tracialSequenceValue τ ω (star x * x)
    rw [hx] at hlim
    have ht := (Real.continuous_sqrt.tendsto 0).comp
      ((Complex.continuous_re.tendsto 0).comp hlim)
    simpa only [TraceNullSequence, Function.comp_def, lp.infty_coeFn_mul, lp.coeFn_star,
      Pi.mul_apply, Pi.star_apply, Complex.zero_re, Real.sqrt_zero, traceTwoNorm] using ht
  · intro hx
    exact tracialSequenceValue_eq_zero_of_null τ ω
      (traceNullSequence_mul_left τ ω (star x) hx)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialSequenceQuotient
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.traceCenter_apply _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.traceTwoNorm_eq_zero_iff _root_.OAI.KadisonKastler.traceTwoNorm_neg _root_.OAI.KadisonKastler.traceTwoNorm_zero _root_.OAI.KadisonKastler.trace_traceCenter _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The faithful trace on the tracial sequence quotient -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ)

abbrev TracialSequenceQuotient := (traceNullClosedIdeal τ ω).Quotient

local instance tracialSequenceProductOrder : PartialOrder (VaryingBoundedSequence B) :=
  CStarAlgebra.spectralOrder _
local instance tracialSequenceProductStarOrder : StarOrderedRing (VaryingBoundedSequence B) :=
  CStarAlgebra.spectralOrderedRing _

instance tracialSequenceQuotientCStarAlgebra : CStarAlgebra (TracialSequenceQuotient τ ω) :=
  inferInstanceAs (CStarAlgebra (traceNullClosedIdeal τ ω).Quotient)

def tracialSequenceQuotientMap :
    VaryingBoundedSequence B →⋆ₐ[ℂ] TracialSequenceQuotient τ ω :=
  (traceNullClosedIdeal τ ω).quotientStarHom

theorem tracialSequenceQuotientMap_surjective :
    Function.Surjective (tracialSequenceQuotientMap τ ω) :=
  (traceNullClosedIdeal τ ω).quotientMap_surjective

theorem tracialSequenceQuotientMap_eq_zero_iff (x : VaryingBoundedSequence B) :
    tracialSequenceQuotientMap τ ω x = 0 ↔ TraceNullSequence τ ω x := by
  change (traceNullClosedIdeal τ ω).quotientMap x =
    (traceNullClosedIdeal τ ω).quotientMap 0 ↔ _
  constructor
  · intro h
    have hh := Quotient.exact h
    change TraceNullSequence τ ω (x - 0) at hh
    simpa only [sub_zero] using hh
  · intro h
    apply Quotient.sound
    change TraceNullSequence τ ω (x - 0)
    simpa only [sub_zero] using h

def tracialQuotientLinear : TracialSequenceQuotient τ ω →ₗ[ℂ] ℂ where
  toFun := Quotient.lift (tracialSequenceValue τ ω) (by
    intro x y h
    change TraceNullSequence τ ω (x - y) at h
    have he := tracialSequenceValue_eq_zero_of_null τ ω h
    change tracialSequenceLinear τ ω (x - y) = 0 at he
    rw [map_sub] at he
    exact sub_eq_zero.mp he)
  map_add' x y := by
    obtain ⟨a, rfl⟩ := tracialSequenceQuotientMap_surjective τ ω x
    obtain ⟨b, rfl⟩ := tracialSequenceQuotientMap_surjective τ ω y
    change tracialSequenceValue τ ω (a + b) = _
    exact (tracialSequenceLinear τ ω).map_add a b
  map_smul' c x := by
    obtain ⟨a, rfl⟩ := tracialSequenceQuotientMap_surjective τ ω x
    change tracialSequenceValue τ ω (c • a) = _
    exact (tracialSequenceLinear τ ω).map_smul c a

@[simp] theorem tracialQuotientLinear_map (x : VaryingBoundedSequence B) :
    tracialQuotientLinear τ ω (tracialSequenceQuotientMap τ ω x) =
      tracialSequenceValue τ ω x := rfl

/-- The quotient trace is faithful because exactly the two-null ideal was removed. -/
def tracialQuotientTrace : FaithfulTracialState (TracialSequenceQuotient τ ω) where
  toLinearMap := tracialQuotientLinear τ ω
  map_one := tracialSequenceValue_one τ ω
  positive x := by
    obtain ⟨a, rfl⟩ := tracialSequenceQuotientMap_surjective τ ω x
    rw [← map_star, ← map_mul, tracialQuotientLinear_map]
    exact tracialSequenceValue_positive τ ω a
  positive_im x := by
    obtain ⟨a, rfl⟩ := tracialSequenceQuotientMap_surjective τ ω x
    rw [← map_star, ← map_mul, tracialQuotientLinear_map]
    exact tracialSequenceValue_positive_im τ ω a
  faithful x hx := by
    obtain ⟨a, rfl⟩ := tracialSequenceQuotientMap_surjective τ ω x
    rw [← map_star, ← map_mul, tracialQuotientLinear_map] at hx
    exact (tracialSequenceQuotientMap_eq_zero_iff τ ω a).mpr
      ((tracialSequenceValue_square_eq_zero_iff τ ω a).mp hx)
  tracial x y := by
    obtain ⟨a, rfl⟩ := tracialSequenceQuotientMap_surjective τ ω x
    obtain ⟨b, rfl⟩ := tracialSequenceQuotientMap_surjective τ ω y
    rw [← map_mul, ← map_mul, tracialQuotientLinear_map, tracialQuotientLinear_map]
    exact tracialSequenceValue_tracial τ ω a b

/-- The constructed quotient has the required coordinate trace formula. -/
theorem tracialQuotientTrace_limit (x : VaryingBoundedSequence B) :
    Tendsto (fun j => (τ j).toLinearMap (x j)) (ω : Filter ℕ)
      (𝓝 ((tracialQuotientTrace τ ω).toLinearMap (tracialSequenceQuotientMap τ ω x))) :=
  tendsto_tracialSequenceValue τ ω x

/-- Coordinate two-norms converge to the quotient two-norm. -/
theorem tracialQuotientTwoNorm_limit (x : VaryingBoundedSequence B) :
    Tendsto (fun j => traceTwoNorm (τ j) (x j)) (ω : Filter ℕ)
      (𝓝 (traceTwoNorm (tracialQuotientTrace τ ω) (tracialSequenceQuotientMap τ ω x))) := by
  have ht := (Real.continuous_sqrt.tendsto _).comp
    ((Complex.continuous_re.tendsto _).comp (tracialQuotientTrace_limit τ ω (star x * x)))
  simpa only [Function.comp_def, traceTwoNorm, lp.infty_coeFn_mul, lp.coeFn_star,
    Pi.mul_apply, Pi.star_apply, map_mul, map_star] using ht

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialDiagonalLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.traceCenter_apply _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.traceTwoNorm_eq_zero_iff _root_.OAI.KadisonKastler.traceTwoNorm_neg _root_.OAI.KadisonKastler.traceTwoNorm_zero _root_.OAI.KadisonKastler.trace_traceCenter _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded diagonal limits in the tracial sequence quotient -/

namespace KadisonKastler

open Filter Set
open scoped Topology

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ)

/-- A uniformly bounded, rapidly two-Cauchy family has a coordinatewise
diagonal representative with the same uniform bound. -/
theorem exists_tracial_diagonal_limit (hω : (ω : Filter ℕ) ≤ atTop)
    (x : ℕ → VaryingBoundedSequence B) (C : ℝ) (hC : 0 ≤ C)
    (hx : ∀ n j, ‖x n j‖ ≤ C) (a : ℕ → ℝ)
    (hfast : ∀ n m, n ≤ m → traceTwoNorm (tracialQuotientTrace τ ω)
      (tracialSequenceQuotientMap τ ω (x m) - tracialSequenceQuotientMap τ ω (x n)) < a n) :
    ∃ y : VaryingBoundedSequence B, ‖y‖ ≤ C ∧ ∀ n,
      traceTwoNorm (tracialQuotientTrace τ ω)
        (tracialSequenceQuotientMap τ ω y - tracialSequenceQuotientMap τ ω (x n)) ≤ a n := by
  classical
  let A : ℕ → Set ℕ := fun m => {j | ∀ n ≤ m, traceTwoNorm (τ j) (x m j - x n j) < a n}
  have hA (m : ℕ) : A m ∈ ω := by
    have he : ∀ᶠ j in (ω : Filter ℕ), ∀ n ∈ Finset.range (m + 1),
        traceTwoNorm (τ j) (x m j - x n j) < a n := by
      apply (eventually_all_finset _).mpr
      intro n hn
      have ht := (tracialQuotientTwoNorm_limit τ ω (x m - x n)).eventually
        (gt_mem_nhds (by simpa only [map_sub] using hfast n m (by simpa using hn)))
      exact ht
    filter_upwards [he] with j hj n hn
    exact hj n (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  obtain ⟨k, hk, hAk⟩ := exists_ultrafilter_diagonal_index ω hω A hA
  let y : VaryingBoundedSequence B := ⟨fun j => x (k j) j,
    memℓp_infty ⟨C, by rintro _ ⟨j, rfl⟩; exact hx (k j) j⟩⟩
  refine ⟨y, lp.norm_le_of_forall_le hC (fun j => hx (k j) j), ?_⟩
  intro n
  have he : ∀ᶠ j in (ω : Filter ℕ), traceTwoNorm (τ j) (y j - x n j) ≤ a n := by
    filter_upwards [hAk, (tendsto_atTop.mp hk) n] with j hj hjn
    exact (hj n hjn).le
  have ht := tracialQuotientTwoNorm_limit τ ω (y - x n)
  rw [map_sub] at ht
  exact le_of_tendsto ht he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialQuotientCompleteness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.traceCenter_apply _root_.OAI.KadisonKastler.traceTwoNorm_eq_zero_iff _root_.OAI.KadisonKastler.traceTwoNorm_neg _root_.OAI.KadisonKastler.traceTwoNorm_zero _root_.OAI.KadisonKastler.trace_traceCenter _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Two-norm completeness on bounded sets of the tracial quotient -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ)

local notation "Q" => TracialSequenceQuotient τ ω
local notation "φ" => tracialQuotientTrace τ ω
local instance instPartialOrderTracialSequenceQuotient : PartialOrder Q := CStarAlgebra.spectralOrder _
local instance instStarOrderedRingTracialSequenceQuotient : StarOrderedRing Q := CStarAlgebra.spectralOrderedRing _

/-- Every operator-norm-bounded two-Cauchy sequence has its GNS limit in
this quotient. A one-unit norm slack suffices for the subsequent closure proof. -/
theorem tracialQuotient_bounded_complete (hω : (ω : Filter ℕ) ≤ atTop)
    (a : ℕ → Q) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C)
    (hc : CauchySeq (fun n => traceStateVector φ (a n))) :
    ∃ b : Q, ‖b‖ ≤ C + 1 ∧
      Tendsto (fun n => traceStateVector φ (a n)) atTop (𝓝 (traceStateVector φ b)) := by
  obtain ⟨f, hf, hfast⟩ := Metric.exists_subseq_bounded_of_cauchySeq
    (fun n => traceStateVector φ (a n)) hc (fun n => 1 / (n + 1 : ℝ))
    (fun n => by positivity)
  have hlift (n : ℕ) : ∃ x : VaryingBoundedSequence B,
      tracialSequenceQuotientMap τ ω x = a (f n) ∧ ‖x‖ < ‖a (f n)‖ + 1 :=
    (traceNullClosedIdeal τ ω).quotient_norm_lt_rep (a (f n)) (by norm_num)
  choose x hx hxn using hlift
  have hcoord (n j : ℕ) : ‖x n j‖ ≤ C + 1 :=
    (varyingSequence_norm_apply_le (x n) j).trans
      ((hxn n).le.trans (add_le_add (ha (f n)) le_rfl))
  have htwo (n m : ℕ) (hnm : n ≤ m) :
      traceTwoNorm φ (tracialSequenceQuotientMap τ ω (x m) -
        tracialSequenceQuotientMap τ ω (x n)) < 1 / (n + 1 : ℝ) := by
    rw [hx, hx, ← norm_traceStateVector, traceStateVector_sub, ← dist_eq_norm]
    exact hfast n (f m) (hf.monotone hnm)
  obtain ⟨y, hyn, hy⟩ := exists_tracial_diagonal_limit τ ω hω x (C + 1)
    (by positivity) hcoord (fun n => 1 / (n + 1 : ℝ)) htwo
  let b := tracialSequenceQuotientMap τ ω y
  have hb : ‖b‖ ≤ C + 1 :=
    (NonUnitalStarAlgHom.norm_apply_le (tracialSequenceQuotientMap τ ω) y).trans hyn
  refine ⟨b, hb, tendsto_nhds_of_cauchySeq_of_subseq hc hf.tendsto_atTop ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg))
    (Eventually.of_forall (fun n => ?_)) tendsto_one_div_add_atTop_nhds_zero_nat
  change dist (traceStateVector φ (a (f n))) (traceStateVector φ b) ≤ _
  rw [dist_comm, dist_eq_norm, ← traceStateVector_sub, norm_traceStateVector]
  exact (by simpa only [hx] using hy n)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialQuotientVonNeumann
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The tracial sequence quotient is a represented von Neumann algebra -/

namespace KadisonKastler

open Filter Set
open scoped Topology

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ)

local notation "Q" => TracialSequenceQuotient τ ω
local notation "φ" => tracialQuotientTrace τ ω
local instance instPartialOrderTracialSequenceQuotient_1 : PartialOrder Q := CStarAlgebra.spectralOrder _
local instance instStarOrderedRingTracialSequenceQuotient_1 : StarOrderedRing Q := CStarAlgebra.spectralOrderedRing _
local notation "K" => TraceStateHilbert φ
local notation "π" => traceStateRepresentation φ
local notation "ι" => traceStateVector φ

def tracialSequenceAlgebra : VonNeumannAlgebra K :=
  generatedVonNeumannAlgebra (traceStateRepresentation φ).range

/-- A contraction in the bicommutant is recovered by bounded two-completeness. -/
theorem tracialSequenceAlgebra_contraction_in_range (hω : (ω : Filter ℕ) ≤ atTop)
    (T : K →L[ℂ] K) (hT : T ∈ tracialSequenceAlgebra τ ω) (hn : ‖T‖ ≤ 1) :
    ∃ b : Q, π b = T := by
  classical
  have ht : T ∈ Set.centralizer (Set.centralizer ((traceStateRepresentation φ).range : Set (K →L[ℂ] K))) := by
    change T ∈ (generatedVonNeumannAlgebra (traceStateRepresentation φ).range : Set (K →L[ℂ] K)) at hT
    rwa [generatedVonNeumannAlgebra_coe] at hT
  have happ (n : ℕ) : ∃ b : Q, ‖b‖ ≤ 1 ∧ ‖T (ι 1) - ι b‖ < 1 / (n + 1 : ℝ) := by
    obtain ⟨S, hSn, hS⟩ := publishedKaplanskyDensity K (traceStateRepresentation φ).range T ht hn
      {ι 1} (1 / (n + 1 : ℝ)) (by positivity)
    obtain ⟨b, hb⟩ := S.property
    change π b = S.val at hb
    refine ⟨b, ?_, ?_⟩
    · rw [← norm_traceStateRepresentation φ b, hb]
      exact hSn
    · have h := hS (ι 1) (Finset.mem_singleton_self _)
      rw [← hb, traceStateRepresentation_vector, mul_one] at h
      exact h
  choose a han ha using happ
  have halim : Tendsto (fun n => ι (a n)) atTop (𝓝 (T (ι 1))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg))
      (Eventually.of_forall (fun n => ?_)) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [dist_eq_norm, norm_sub_rev] using (ha n).le
  obtain ⟨b, _, hb⟩ := tracialQuotient_bounded_complete τ ω hω a 1 zero_le_one han halim.cauchySeq
  have hbone : ι b = T (ι 1) := tendsto_nhds_unique hb halim
  refine ⟨b, ?_⟩
  apply DFunLike.ext'
  apply (traceStateVector_dense φ).equalizer (π b).continuous T.continuous
  funext a
  have hcomm : traceStateRight φ a * T = T * traceStateRight φ a := by
    apply ht
    intro S hS
    obtain ⟨c, rfl⟩ := hS
    exact (traceState_left_right_commute φ c a).eq
  have hcommv := congrArg (fun R : K →L[ℂ] K => R (ι 1)) hcomm
  change π b (ι a) = T (ι a)
  simpa only [mul_apply_eq_comp, traceStateRight_vector, one_mul,
    ← hbone, traceStateRepresentation_vector] using hcommv

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialQuotientRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.traceCenter_apply _root_.OAI.KadisonKastler.traceTwoNorm_eq_zero_iff _root_.OAI.KadisonKastler.traceTwoNorm_neg _root_.OAI.KadisonKastler.traceTwoNorm_zero _root_.OAI.KadisonKastler.trace_traceCenter _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The trace-preserving represented tracial quotient -/

namespace KadisonKastler

open Filter

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ)

local notation "Q" => TracialSequenceQuotient τ ω
local notation "φ" => tracialQuotientTrace τ ω
local instance instPartialOrderTracialSequenceQuotient_2 : PartialOrder Q := CStarAlgebra.spectralOrder _
local instance instStarOrderedRingTracialSequenceQuotient_2 : StarOrderedRing Q := CStarAlgebra.spectralOrderedRing _
local notation "K" => TraceStateHilbert φ
local notation "π" => traceStateRepresentation φ

theorem tracialSequenceAlgebra_in_range (hω : (ω : Filter ℕ) ≤ atTop)
    (T : K →L[ℂ] K) (hT : T ∈ tracialSequenceAlgebra τ ω) : ∃ b : Q, π b = T := by
  by_cases hzero : T = 0
  · exact ⟨0, by rw [map_zero, hzero]⟩
  have hn : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
  have hsmall : ‖(‖T‖ : ℂ)⁻¹ • T‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg T), inv_mul_cancel₀ hn]
  obtain ⟨a, ha⟩ := tracialSequenceAlgebra_contraction_in_range τ ω hω
    ((‖T‖ : ℂ)⁻¹ • T) ((tracialSequenceAlgebra τ ω).toStarSubalgebra.smul_mem hT _) hsmall
  refine ⟨(‖T‖ : ℂ) • a, ?_⟩
  rw [map_smul, ha, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn), one_smul]

theorem tracialSequenceRepresentation_mem (a : Q) : π a ∈ tracialSequenceAlgebra τ ω :=
  subset_generatedVonNeumannAlgebra _ ⟨a, rfl⟩

attribute [local irreducible] tracialSequenceAlgebra

def tracialSequenceHom : Q →⋆ₐ[ℂ] Algebra (tracialSequenceAlgebra τ ω) :=
  (traceStateRepresentation φ).codRestrict (tracialSequenceAlgebra τ ω).toStarSubalgebra
    (tracialSequenceRepresentation_mem τ ω)

theorem tracialSequenceHom_injective : Function.Injective (tracialSequenceHom τ ω) := by
  intro a b h
  have hv := congrArg Subtype.val h
  change π a = π b at hv
  exact traceStateRepresentation_injective φ hv

theorem tracialSequenceHom_surjective (hω : (ω : Filter ℕ) ≤ atTop) :
    Function.Surjective (tracialSequenceHom τ ω) :=
  starAlgHom_codRestrict_surjective (traceStateRepresentation φ)
    (tracialSequenceAlgebra τ ω).toStarSubalgebra _
    (tracialSequenceAlgebra_in_range (B := B) τ ω hω)

def tracialSequenceEquiv (hω : (ω : Filter ℕ) ≤ atTop) :
    Q ≃⋆ₐ[ℂ] Algebra (tracialSequenceAlgebra τ ω) :=
  StarAlgEquiv.ofBijective (tracialSequenceHom τ ω)
    ⟨tracialSequenceHom_injective τ ω, tracialSequenceHom_surjective τ ω hω⟩

@[simp] theorem tracialSequenceEquiv_coe (hω : (ω : Filter ℕ) ≤ atTop) (a : Q) :
    (tracialSequenceEquiv τ ω hω a).val = π a := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioReindex
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reindexing the extra family of lambda sites

Even and odd lambda sites absorb a second countable family. Mu sites
are unchanged. This is the explicit state-preserving bijection used in
the pointed infinite tensor-product absorption argument.
-/

namespace KadisonKastler

noncomputable section

def twoRatioSiteParameter : TwoRatioSite → ℝ :=
  Sum.elim (fun _ => fixedProductLambda) (fun _ => fixedProductMu)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeICyclicRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The irreducible cyclic representation afforded by a minimal projection

A nonzero vector in a minimal projection determines a faithful irreducible
cyclic representation of a factor.  The construction uses the actual closed
orbit in the given Hilbert space; no classification theorem is invoked.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

abbrev typeICyclicSpace (M : VonNeumannAlgebra H) (ξ : H) :=
  vectorOrbitClosure M.toStarSubalgebra ξ

def typeICyclicVector (M : VonNeumannAlgebra H) (ξ : H) : typeICyclicSpace M ξ :=
  ⟨ξ, mem_vectorOrbitClosure _ _⟩

end

end KadisonKastler

end OAI
end


