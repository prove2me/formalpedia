-- Prove2me | Definitions.Def_Q260K011
-- name    : Q260K011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:42:28.615725+00:00
-- url     : https://prove2.me/theorems/14422d0e-a73d-46fa-bd9b-af188a3c5684
-- title:
--   Definitions bundle Q260K011 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 40 declarations of OpenAI's Lean: 13 definitions, 4 instances and 23 theorems. The definitions and types are `OAI.KadisonKastler.FullMatrixCorner.partialDiagonal`, `OAI.KadisonKastler.WeakOperatorField`, `OAI.KadisonKastler.WeakOperatorField.pullback`, `OAI.KadisonKastler.WeakOperatorField.pullbackValue`, `OAI.KadisonKastler.WeakOperatorField.representative`, `OAI.KadisonKastler.canonicalCoordinate`, `OAI.KadisonKastler.canonicalInitialEquiv`, `OAI.KadisonKastler.canonicalInitialSpace`, `OAI.KadisonKastler.canonicalMatrixUnit`, `OAI.KadisonKastler.canonicalSingle`, `OAI.KadisonKastler.operatorFieldConst`, `OAI.KadisonKastler.operatorFieldQuotient`, `OAI.KadisonKastler.operatorFieldZeroIdeal`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`KadisonKastler_BaireMeasurableBranch`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/BaireMeasurableBranch.lean), [`KadisonKastler_BoundedSequence`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/BoundedSequence.lean), [`KadisonKastler_CanonicalMatrixCorner`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/CanonicalMatrixCorner.lean), [`KadisonKastler_InflatedConjugacy`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/InflatedConjugacy.lean), [`KadisonKastler_MatrixSequences`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/MatrixSequences.lean), [`KadisonKastler_WeakFieldCoefficients`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/WeakFieldCoefficients.lean), [`KadisonKastler_WeakFieldNorm`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/WeakFieldNorm.lean), [`KadisonKastler_WeakFieldPullback`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/WeakFieldPullback.lean), [`KadisonKastler_WeakOperatorFields`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/WeakOperatorFields.lean).
--
--   **Imports.** It imports the bundles `Q260K000`, `Q260K002`, `Q260K003` and `Q260K005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K017`; the statements `OAI.KadisonKastler.operatorFieldConst_representative_ae` and `OAI.KadisonKastler.weakOperatorField_closed_projection_span_eq_top`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.Rat
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
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
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
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
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
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Fin.Basic
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
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Tactic
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
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
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K000
import Definitions.Def_Q260K002
import Definitions.Def_Q260K003
import Definitions.Def_Q260K005

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BaireMeasurableBranch
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable successive choices of Baire digits -/

namespace KadisonKastler

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]

instance instMeasurableSingletonClassListNat_solutions : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundedSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Bounded sequences, spectral clipping and trace-to-strong transfer

The sequence algebra is the ordinary C*-algebra of bounded functions on
the discrete natural numbers. Evaluation commutes with the spectral
cutoff. A trace quotient therefore kills the discarded part as soon as
the quotient norm satisfies the desired cutoff bound.
-/

namespace KadisonKastler

open Filter
open scoped Topology BoundedContinuousFunction

noncomputable section

instance boundedSequenceCStarAlgebra {B : Type*} [CStarAlgebra B] :
    CStarAlgebra (BoundedSequence B) where

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CanonicalMatrixCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The canonical countable matrix corner

The coordinate injections and evaluations on the Hilbert direct sum give
actual matrix units.  Their initial corner is canonically isometric to
the original Hilbert space, and their diagonal projections sum strongly
to the identity.
-/

namespace KadisonKastler

noncomputable section

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def canonicalSingle (i : ℕ) : H →L[ℂ] CountableHilbertSum H :=
  lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 i

def canonicalCoordinate (i : ℕ) : CountableHilbertSum H →L[ℂ] H :=
  lp.evalCLM ℂ (fun _ : ℕ => H) 2 i

@[simp] theorem canonicalSingle_apply (i : ℕ) (x : H) :
    canonicalSingle H i x = lp.single 2 i x := rfl

@[simp] theorem canonicalCoordinate_apply (i : ℕ) (x : CountableHilbertSum H) :
    canonicalCoordinate H i x = x i := rfl

def canonicalMatrixUnit (i j : ℕ) : CountableHilbertSum H →L[ℂ] CountableHilbertSum H :=
  (canonicalSingle H i).comp (canonicalCoordinate H j)

@[simp] theorem canonicalMatrixUnit_apply (i j : ℕ) (x : CountableHilbertSum H) :
    canonicalMatrixUnit H i j x = lp.single 2 i (x j) := rfl

theorem canonicalMatrixUnit_mul (i j k l : ℕ) :
    canonicalMatrixUnit H i j * canonicalMatrixUnit H k l =
      if j = k then canonicalMatrixUnit H i l else 0 := by
  ext x m
  by_cases h : j = k
  · subst k
    simp [mul_apply_eq_comp, canonicalMatrixUnit_apply, lp.single_apply]
  · simp [mul_apply_eq_comp, canonicalMatrixUnit_apply, lp.single_apply, h]

/-- The closed subspace supported at coordinate zero. -/
def canonicalInitialSpace : Submodule ℂ (CountableHilbertSum H) :=
  (canonicalSingle H 0).range

@[simp] theorem mem_canonicalInitialSpace (x : CountableHilbertSum H) :
    x ∈ canonicalInitialSpace H ↔ ∃ y : H, lp.single 2 0 y = x := Iff.rfl

/-- The initial coordinate has exactly the original Hilbert norm. -/
def canonicalInitialEquiv : H ≃ₗᵢ[ℂ] canonicalInitialSpace H where
  toFun x := ⟨lp.single 2 0 x, x, rfl⟩
  invFun x := x.val 0
  left_inv x := by simp [lp.single_apply]
  right_inv x := by
    apply Subtype.ext
    obtain ⟨y, hy⟩ := x.property
    change lp.single 2 0 (x.val 0) = x.val
    rw [← hy]
    simp [canonicalSingle, lp.single_apply]
  map_add' x y := by
    apply Subtype.ext
    exact map_add (canonicalSingle H 0) x y
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (canonicalSingle H 0) c x
  norm_map' x := by
    change ‖(lp.single 2 0 x : CountableHilbertSum H)‖ = ‖x‖
    exact lp.norm_single (E := fun _ : ℕ => H) (p := 2) (by norm_num) 0 x

@[simp] theorem canonicalInitialEquiv_apply (x : H) :
    (canonicalInitialEquiv H x : CountableHilbertSum H) = lp.single 2 0 x := rfl

@[simp] theorem canonicalInitialEquiv_symm_apply (x : canonicalInitialSpace H) :
    (canonicalInitialEquiv H).symm x = x.val 0 := rfl

variable [CompleteSpace H]

instance canonicalInitialSpaceComplete : CompleteSpace (canonicalInitialSpace H) :=
  ((canonicalInitialEquiv H).symm.isometry.isUniformInducing.completeSpace_congr
    (canonicalInitialEquiv H).symm.surjective).mpr inferInstance

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InflatedConjugacy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering the full algebra from its common matrix corners -/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

def partialDiagonal (s : Finset ℕ) : H →L[ℂ] H := ∑ i ∈ s, F.entry i i

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixSequences
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite matrices and bounded sequences

Entrywise evaluation identifies bounded sequences of finite matrices
with finite matrices of bounded sequences. Applying a tracial quotient
to the entries gives the normalized matrix trace formula.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators BoundedContinuousFunction

noncomputable section

variable {B C ι : Type*} [CStarAlgebra B] [CStarAlgebra C] [Fintype ι] [DecidableEq ι]

local instance matrixSequencesOrder_r18e081_1 : PartialOrder B := CStarAlgebra.spectralOrder _
local instance matrixSequencesStarOrder_r18e081_1 : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _
attribute [local instance] OAI.KadisonKastler.matrixSequencesTargetOrder
local instance matrixSequencesTargetStarOrder : StarOrderedRing C := CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakOperatorFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Essentially bounded weak operator fields

The representatives are bounded operator-valued functions with measurable
evaluations of the function and its adjoint. Their closed C-star algebra
is quotiented by the closed star ideal of almost-everywhere zero fields.
The resulting norm is bounded by every essential operator-norm bound.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

noncomputable section

variable {D H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [MeasurableSpace D] (μ : Measure D)

/-- The zero fields form a closed two-sided star ideal. -/
def operatorFieldZeroIdeal :
    CuntzPureness.ClosedStarIdeal (WeakOperatorRepresentative (H := H) μ) where
  ideal := TwoSidedIdeal.ofRingCon (operatorFieldAERel μ)
  star_mem {F} hF := by
    change WeakOperatorRepresentative.eval (star F) =ᵐ[μ] fun _ => 0
    change WeakOperatorRepresentative.eval F =ᵐ[μ] fun _ => 0 at hF
    filter_upwards [hF] with x hx
    simp only [WeakOperatorRepresentative.eval_star, hx, star_zero]
  isClosed := by
    apply IsSeqClosed.isClosed
    intro F G hF hG
    change WeakOperatorRepresentative.eval G =ᵐ[μ] fun _ => 0
    have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, WeakOperatorRepresentative.eval (F n) x = 0 :=
      ae_all_iff.mpr hF
    filter_upwards [hall] with x hx
    have ht := ((WeakOperatorRepresentative.eval_continuous x).tendsto G).comp hG
    have hz : Tendsto (fun n : ℕ => WeakOperatorRepresentative.eval (F n) x) atTop (𝓝 0) := by
      simpa only [hx] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : H →L[ℂ] H)) atTop (𝓝 0))
    exact tendsto_nhds_unique ht hz

attribute [local instance] OAI.KadisonKastler.weakOperatorRepresentativeOrder
attribute [local instance] OAI.KadisonKastler.weakOperatorRepresentativeStarOrder
abbrev WeakOperatorField := (operatorFieldZeroIdeal (H := H) μ).Quotient

instance weakOperatorFieldCStar : CStarAlgebra (WeakOperatorField (H := H) μ) := inferInstance

def operatorFieldQuotient : WeakOperatorRepresentative (H := H) μ →⋆ₐ[ℂ]
    WeakOperatorField (H := H) μ := (operatorFieldZeroIdeal μ).quotientStarHom

theorem operatorFieldQuotient_surjective : Function.Surjective (operatorFieldQuotient (H := H) μ) :=
  (operatorFieldZeroIdeal μ).quotientMap_surjective

theorem operatorFieldQuotient_eq_iff (F G : WeakOperatorRepresentative (H := H) μ) :
    operatorFieldQuotient μ F = operatorFieldQuotient μ G ↔
      WeakOperatorRepresentative.eval F =ᵐ[μ] WeakOperatorRepresentative.eval G := by
  change (operatorFieldAERel (H := H) μ).mk' F = (operatorFieldAERel (H := H) μ).mk' G ↔ _
  exact Quotient.eq

theorem operatorFieldQuotient_norm_le (F : WeakOperatorRepresentative (H := H) μ) :
    ‖operatorFieldQuotient μ F‖ ≤ ‖F‖ := (operatorFieldZeroIdeal μ).quotientMap_norm_le F

def operatorFieldConst : (H →L[ℂ] H) →⋆ₐ[ℂ] WeakOperatorField (H := H) μ :=
  (operatorFieldQuotient μ).comp (operatorRepresentativeConst μ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakFieldNorm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_pullback _root_.OAI.KadisonKastler.WeakOperatorRepresentative.pullback_constant _root_.OAI.KadisonKastler.WeakOperatorRepresentative.pullback_id _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The quotient norm is the essential operator norm

The general Banach quotient supplies arbitrarily close representatives.
A countable intersection gives the exact essential bound, and cutting off
its exceptional set produces a norm-minimizing representative.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every representative satisfies its quotient norm bound almost everywhere. -/
theorem operatorField_ae_norm_le (F : WeakOperatorRepresentative (H := H) μ) :
    ∀ᵐ x ∂μ, ‖WeakOperatorRepresentative.eval F x‖ ≤ ‖operatorFieldQuotient μ F‖ := by
  have hn (n : ℕ) : ∀ᵐ x ∂μ, ‖WeakOperatorRepresentative.eval F x‖ ≤
      ‖operatorFieldQuotient μ F‖ + 1 / (n + 1 : ℝ) := by
    obtain ⟨G, hG, hnorm⟩ := (operatorFieldZeroIdeal (H := H) μ).quotient_norm_lt_rep
      (operatorFieldQuotient μ F) (one_div_pos.mpr (by positivity : 0 < (n + 1 : ℝ)))
    have heq : WeakOperatorRepresentative.eval G =ᵐ[μ] WeakOperatorRepresentative.eval F :=
      (operatorFieldQuotient_eq_iff μ G F).mp hG
    filter_upwards [heq] with x hx
    rw [← hx]
    exact (WeakOperatorRepresentative.eval_norm_le G x).trans hnorm.le
  filter_upwards [ae_all_iff.mpr hn] with x hx
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  exact (hx n).trans (by linarith)

/-- The actual weak-operator quotient admits representatives attaining its norm. -/
theorem exists_operatorFieldRepresentative (T : WeakOperatorField (H := H) μ) :
    ∃ F : WeakOperatorRepresentative (H := H) μ,
      operatorFieldQuotient μ F = T ∧ ‖F‖ ≤ ‖T‖ := by
  classical
  obtain ⟨F, rfl⟩ := operatorFieldQuotient_surjective (H := H) μ T
  let C := ‖operatorFieldQuotient μ F‖
  let f : D → H →L[ℂ] H := fun x =>
    if ‖WeakOperatorRepresentative.eval F x‖ ≤ C then WeakOperatorRepresentative.eval F x else 0
  have hnorm (x : D) : ‖f x‖ ≤ C := by
    dsimp [f]
    split_ifs with hx
    · exact hx
    · simpa only [norm_zero] using norm_nonneg (operatorFieldQuotient μ F)
  have heq : WeakOperatorRepresentative.eval F =ᵐ[μ] f :=
    (operatorField_ae_norm_le F).mono fun x hx => by simp [f, C, hx]
  have hm (ξ : H) : AEStronglyMeasurable (fun x => f x ξ) μ :=
    (WeakOperatorRepresentative.eval_aestronglyMeasurable F ξ).congr
      (heq.mono fun _ hx => congrArg (fun T => T ξ) hx)
  have hs (ξ : H) : AEStronglyMeasurable (fun x => star (f x) ξ) μ :=
    (WeakOperatorRepresentative.star_eval_aestronglyMeasurable F ξ).congr
      (heq.mono fun _ hx => congrArg (fun T : H →L[ℂ] H => star T ξ) hx)
  let G := WeakOperatorRepresentative.mk f C hnorm hm hs
  refine ⟨G, ?_, WeakOperatorRepresentative.norm_mk_le f (norm_nonneg _) hnorm hm hs⟩
  exact ((operatorFieldQuotient_eq_iff μ F G).mpr heq).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakFieldCoefficients
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Intrinsic scalar coefficients of weak operator fields -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorField

/-- A representative with exactly the quotient norm bound. -/
def representative (T : WeakOperatorField (H := H) μ) : WeakOperatorRepresentative (H := H) μ :=
  Classical.choose (exists_operatorFieldRepresentative T)

theorem quotient_representative (T : WeakOperatorField (H := H) μ) :
    operatorFieldQuotient μ (representative T) = T :=
  (Classical.choose_spec (exists_operatorFieldRepresentative T)).1

theorem norm_representative_le (T : WeakOperatorField (H := H) μ) :
    ‖representative T‖ ≤ ‖T‖ :=
  (Classical.choose_spec (exists_operatorFieldRepresentative T)).2

end WeakOperatorField

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakFieldPullback
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nonsingular pullback of weak operator fields

Composition preserves the measurable representatives and their uniform
bound. Nonsingularity makes the construction independent of representatives.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorField

def pullbackValue (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (q : WeakOperatorField (H := H) μ) : WeakOperatorField (H := H) μ :=
  operatorFieldQuotient (H := H) μ (WeakOperatorRepresentative.pullback (H := H) T hT (representative q))

theorem pullbackValue_quotient (T : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ)
    (F : WeakOperatorRepresentative (H := H) μ) :
    pullbackValue (H := H) T hT (operatorFieldQuotient (H := H) μ F) =
      operatorFieldQuotient (H := H) μ (WeakOperatorRepresentative.pullback (H := H) T hT F) := by
  apply (operatorFieldQuotient_eq_iff μ _ _).mpr
  exact WeakOperatorRepresentative.pullback_congr_ae T hT
    ((operatorFieldQuotient_eq_iff μ _ _).mp (quotient_representative _))

theorem pullbackValue_one (T : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ) :
    pullbackValue (H := H) T hT 1 = 1 := by
    calc
      pullbackValue (H := H) T hT 1 = pullbackValue (H := H) T hT
          (operatorFieldQuotient (H := H) μ (1 : WeakOperatorRepresentative (H := H) μ)) :=
        congrArg (pullbackValue (H := H) T hT) (operatorFieldQuotient (H := H) μ).map_one.symm
      _ = operatorFieldQuotient (H := H) μ (WeakOperatorRepresentative.pullback (H := H) T hT 1) :=
        pullbackValue_quotient T hT _
      _ = 1 := by rw [map_one, map_one]
theorem pullbackValue_mul (T : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ) (q r : WeakOperatorField (H := H) μ) :
    pullbackValue (H := H) T hT (q * r) = pullbackValue (H := H) T hT q * pullbackValue (H := H) T hT r := by
    obtain ⟨F, rfl⟩ := operatorFieldQuotient_surjective (H := H) μ q
    obtain ⟨G, rfl⟩ := operatorFieldQuotient_surjective (H := H) μ r
    rw [← map_mul, pullbackValue_quotient, map_mul, map_mul,
      pullbackValue_quotient, pullbackValue_quotient]
theorem pullbackValue_zero (T : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ) :
    pullbackValue (H := H) T hT 0 = 0 := by
    calc
      pullbackValue (H := H) T hT 0 = pullbackValue (H := H) T hT
          (operatorFieldQuotient (H := H) μ (0 : WeakOperatorRepresentative (H := H) μ)) :=
        congrArg (pullbackValue (H := H) T hT) (operatorFieldQuotient (H := H) μ).map_zero.symm
      _ = operatorFieldQuotient (H := H) μ (WeakOperatorRepresentative.pullback (H := H) T hT 0) :=
        pullbackValue_quotient T hT _
      _ = 0 := by rw [map_zero, map_zero]
theorem pullbackValue_add (T : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ) (q r : WeakOperatorField (H := H) μ) :
    pullbackValue (H := H) T hT (q + r) = pullbackValue (H := H) T hT q + pullbackValue (H := H) T hT r := by
    obtain ⟨F, rfl⟩ := operatorFieldQuotient_surjective (H := H) μ q
    obtain ⟨G, rfl⟩ := operatorFieldQuotient_surjective (H := H) μ r
    rw [← map_add, pullbackValue_quotient, map_add, map_add,
      pullbackValue_quotient, pullbackValue_quotient]
theorem pullbackValue_algebraMap (T : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ) (c : ℂ) :
    pullbackValue (H := H) T hT (algebraMap ℂ (WeakOperatorField (H := H) μ) c) =
      algebraMap ℂ (WeakOperatorField (H := H) μ) c := by
    let a : WeakOperatorRepresentative (H := H) μ :=
      algebraMap ℂ (WeakOperatorRepresentative (H := H) μ) c
    have hq : operatorFieldQuotient (H := H) μ a =
        algebraMap ℂ (WeakOperatorField (H := H) μ) c :=
      (operatorFieldQuotient (H := H) μ).commutes c
    calc
      pullbackValue (H := H) T hT (algebraMap ℂ (WeakOperatorField (H := H) μ) c) =
          pullbackValue (H := H) T hT (operatorFieldQuotient (H := H) μ a) :=
        congrArg (pullbackValue (H := H) T hT) hq.symm
      _ = operatorFieldQuotient (H := H) μ (WeakOperatorRepresentative.pullback (H := H) T hT a) :=
        pullbackValue_quotient T hT a
      _ = operatorFieldQuotient (H := H) μ a := congrArg (operatorFieldQuotient (H := H) μ)
        ((WeakOperatorRepresentative.pullback (H := H) T hT).commutes c)
      _ = algebraMap ℂ (WeakOperatorField (H := H) μ) c := hq
theorem pullbackValue_star (T : D → D)
    (hT : Measure.QuasiMeasurePreserving T μ μ) (q : WeakOperatorField (H := H) μ) :
    pullbackValue (H := H) T hT (star q) = star (pullbackValue (H := H) T hT q) := by
    obtain ⟨F, rfl⟩ := operatorFieldQuotient_surjective (H := H) μ q
    rw [← map_star, pullbackValue_quotient, map_star, map_star, pullbackValue_quotient]

/-- Nonsingular pullback is a unital star-algebra homomorphism of the
actual almost-everywhere quotient. -/
def pullback (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ) :
    WeakOperatorField (H := H) μ →⋆ₐ[ℂ] WeakOperatorField (H := H) μ where
  toFun := pullbackValue (H := H) T hT
  map_one' := pullbackValue_one T hT
  map_mul' := pullbackValue_mul T hT
  map_zero' := pullbackValue_zero T hT
  map_add' := pullbackValue_add T hT
  commutes' := pullbackValue_algebraMap T hT
  map_star' := pullbackValue_star T hT

theorem pullback_quotient (T : D → D) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (F : WeakOperatorRepresentative (H := H) μ) :
    pullback T hT (operatorFieldQuotient (H := H) μ F) =
      operatorFieldQuotient (H := H) μ (WeakOperatorRepresentative.pullback (H := H) T hT F) :=
  pullbackValue_quotient T hT F

end WeakOperatorField

end

end KadisonKastler

end OAI
end


