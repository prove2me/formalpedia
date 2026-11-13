-- Prove2me | Definitions.Def_Q260K009
-- name    : Q260K009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:49:42.940827+00:00
-- url     : https://prove2.me/theorems/1b2855f2-d481-4c89-8232-b6fed3ff8f18
-- title:
--   Definitions bundle Q260K009 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 6 definitions and 24 theorems. The definitions and types are `OAI.Generator.Tracial.EquivalentPartition.rebase`, `OAI.Generator.Tracial.IsDimensionSpectralValue`, `OAI.Generator.Tracial.PartialIsometry.orthogonalPartialSum`, `OAI.Generator.Tracial.PartialIsometry.rangeLink`, `OAI.Generator.Tracial.traceFreeDyadicReference`, `OAI.KadisonKastler.IsMinimalProjectionIn`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_Dimension`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/Dimension.lean), [`FactorGeneration_DyadicComparison`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/DyadicComparison.lean), [`FactorGeneration_FiniteComparison`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/FiniteComparison.lean), [`FactorGeneration_LocalizedStates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/LocalizedStates.lean), [`FactorGeneration_SpectralDimension`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/SpectralDimension.lean), [`FactorGeneration_SpectralStates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/SpectralStates.lean), [`KadisonKastler_HilbertCoefficientMeasurable`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/HilbertCoefficientMeasurable.lean), [`KadisonKastler_PublishedTypeIInjectivity`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/PublishedTypeIInjectivity.lean), [`KadisonKastler_TwoRatioParameters`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/TwoRatioParameters.lean).
--
--   **Imports.** It imports the bundles `OAIQ075A027`, `Q260K003` and `Q260K054` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K017`, `Q260K019` and `Q260K055`; the proofs of `OAI.Generator.Tracial.AlgebraProjection.equivalent_of_le_of_subequivalent` and `OAI_KadisonKastler_mem_closedSubalgebra_of_exp_mem`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
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
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
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
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
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
import Definitions.Def_OAIQ075A027
import Definitions.Def_Q260K003
import Definitions.Def_Q260K054

section
-- module Solutions.OAIQ075_KS.FactorGeneration_FiniteComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! The closed span of algebra translates of a projection range gives its
central support. All operators act on the original Hilbert space; no trace,
cyclic vector, separability, finiteness, or comparison theorem is assumed. -/

/-! The original finiteness predicate excludes proper self-equivalence of a
projection. Projection comparison is connected to the unchanged IsII1Factor
predicate, with no representation, trace, or separability premise. -/

/-! Arbitrary-chain bounds with moving orthogonal initial and final supports, obtained from successive fixed-multiplier weak operator limits without a trace. -/

/-! Complete actual partial isometries to unitaries in a finite factor.
The construction uses projection comparison and finiteness, without a trace. -/
open scoped CStarAlgebra
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.unitaryPolarStarOrder
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hfinite in
theorem PartialIsometry.exists_unitary_extension (v : PartialIsometry M) :
    ∃ u : unitary M.toStarSubalgebra, (u : M.toStarSubalgebra)*v.support.val=v.val := by
  let p : AlgebraProjection M := ⟨1-v.support.val,v.support.property.one_sub⟩
  let q : AlgebraProjection M := ⟨1-v.target.val,v.target.property.one_sub⟩
  obtain ⟨w,hwp,hwq,hw⟩ := traceFree_exists_partialIsometry_comparison hfactor p q
  have hp : v.support.val*w.support.val=0 := by
    calc _ = v.support.val*(p.val*w.support.val) := by rw [hwp]
      _ = (v.support.val*p.val)*w.support.val := (mul_assoc _ _ _).symm
      _ = 0 := by
        change (v.support.val*(1-v.support.val))*w.support.val=0
        rw [v.support.property.mul_one_sub_self,zero_mul]
  have hq : v.target.val*w.target.val=0 := by
    calc _ = v.target.val*(q.val*w.target.val) := by rw [hwq]
      _ = (v.target.val*q.val)*w.target.val := (mul_assoc _ _ _).symm
      _ = 0 := by
        change (v.target.val*(1-v.target.val))*w.target.val=0
        rw [v.target.property.mul_one_sub_self,zero_mul]
  let a := v.patch w hp hq
  have hi : star a.val*a.val=1 := by
    rcases hw with hw | hw
    · rw [a.initial]
      change v.support.val+w.support.val=1
      rw [hw]
      change v.support.val+(1-v.support.val)=1
      abel
    · have hf : a.val*star a.val=1 := by
        change a.target.val=1
        rw [PartialIsometry.patch_target,hw]
        change v.target.val+(1-v.target.val)=1
        abel
      have h := hfinite (star a.val) (by simpa only [star_star] using hf)
      simpa only [star_star] using h
  exact ⟨⟨a.val,⟨hi,hfinite a.val hi⟩⟩,v.le_patch w hp hq⟩

attribute [local instance] OAI.Generator.Tracial.unitaryPolarCStar
attribute [local instance] OAI.Generator.Tracial.unitaryPolarOrder
include hfactor hfinite in
theorem exists_unitary_polar_decomposition (x : M.toStarSubalgebra) :
    ∃ u : unitary M.toStarSubalgebra, (u : M.toStarSubalgebra)*CFC.sqrt (star x*x)=x := by
  obtain ⟨v,hvx,hvi,_⟩ := exists_polar_decomposition x
  let a := CFC.sqrt (star x*x)
  let w : PartialIsometry M := ⟨rangeProjection a,v,hvi⟩
  obtain ⟨u,hu⟩ := w.exists_unitary_extension hfactor hfinite
  have ha : w.support.val*a=a := rangeProjection_mul a
  refine ⟨u,?_⟩
  calc (u : M.toStarSubalgebra)*a = (u : M.toStarSubalgebra)*(w.support.val*a) := by rw [ha]
    _ = w.val*a := by rw [← mul_assoc,hu]
    _ = x := hvx

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_DyadicComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Halving every projection in a diffuse factor without a trace.
Maximality leaves no residual corner: a diffuse residual splits into two
nonzero orthogonal projections, and a polar link gives a strict extension. -/

/-! Finite partitions with explicit equivalence witnesses and compatible binary
refinement. The common initial projection is halved once and its two pieces
are transported to every old piece, so all new pieces remain equivalent. -/

/-! Actual sums of countable orthogonal partial isometries, including least
initial/final support identities. No trace or countable-cofinality premise. -/
namespace Tracial

section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

variable (a : ℕ → PartialIsometry M)
variable (hp : ∀ i j, i ≠ j → (a i).support.val*(a j).support.val=0)
variable (hq : ∀ i j, i ≠ j → (a i).target.val*(a j).target.val=0)

include hp hq in
theorem exists_orthogonalPartialSum (n : ℕ) :
    ∃ v : PartialIsometry M, v.val=∑ i ∈ Finset.range n, (a i).val ∧
      v.support.val=∑ i ∈ Finset.range n, (a i).support.val ∧
      v.target.val=∑ i ∈ Finset.range n, (a i).target.val := by
  induction n with
  | zero => exact ⟨zero, by simp [zero], by simp [zero], by simp [zero,target]⟩
  | succ n ih =>
    obtain ⟨v,hv,hs,ht⟩ := ih
    have ho₁ : v.support.val*(a n).support.val=0 := by
      rw [hs,Finset.sum_mul]
      exact Finset.sum_eq_zero (fun i hi => hp i n (Nat.ne_of_lt (Finset.mem_range.mp hi)))
    have ho₂ : v.target.val*(a n).target.val=0 := by
      rw [ht,Finset.sum_mul]
      exact Finset.sum_eq_zero (fun i hi => hq i n (Nat.ne_of_lt (Finset.mem_range.mp hi)))
    refine ⟨patch v (a n) ho₁ ho₂, ?_, ?_, ?_⟩
    · change v.val+(a n).val=_
      rw [hv,Finset.sum_range_succ]
    · change v.support.val+(a n).support.val=_
      rw [hs,Finset.sum_range_succ]
    · rw [patch_target,ht,Finset.sum_range_succ]

def orthogonalPartialSum (n : ℕ) : PartialIsometry M :=
  (exists_orthogonalPartialSum a hp hq n).choose

theorem orthogonalPartialSum_val (n : ℕ) :
    (orthogonalPartialSum a hp hq n).val=∑ i ∈ Finset.range n, (a i).val :=
  (exists_orthogonalPartialSum a hp hq n).choose_spec.1

theorem orthogonalPartialSum_support (n : ℕ) :
    (orthogonalPartialSum a hp hq n).support.val=∑ i ∈ Finset.range n, (a i).support.val :=
  (exists_orthogonalPartialSum a hp hq n).choose_spec.2.1

theorem orthogonalPartialSum_target (n : ℕ) :
    (orthogonalPartialSum a hp hq n).target.val=∑ i ∈ Finset.range n, (a i).target.val :=
  (exists_orthogonalPartialSum a hp hq n).choose_spec.2.2

theorem le_orthogonalPartialSum (i n : ℕ) (hin : i < n) :
    a i ≤ orthogonalPartialSum a hp hq n := by
  change (orthogonalPartialSum a hp hq n).val*(a i).support.val=(a i).val
  rw [orthogonalPartialSum_val,Finset.sum_mul]
  apply Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hin) _ |>.trans (a i).mul_support
  intro j _ hji
  calc (a j).val*(a i).support.val = ((a j).val*(a j).support.val)*(a i).support.val := by
         rw [(a j).mul_support]
       _ = 0 := by rw [mul_assoc,hp j i hji,mul_zero]

theorem orthogonalPartialSum_monotone : Monotone (orthogonalPartialSum a hp hq) := by
  apply monotone_nat_of_le_succ
  intro n
  let v := orthogonalPartialSum a hp hq n
  have ho₁ : v.support.val*(a n).support.val=0 := by
    rw [orthogonalPartialSum_support,Finset.sum_mul]
    exact Finset.sum_eq_zero (fun i hi => hp i n (Nat.ne_of_lt (Finset.mem_range.mp hi)))
  have ho₂ : v.target.val*(a n).target.val=0 := by
    rw [orthogonalPartialSum_target,Finset.sum_mul]
    exact Finset.sum_eq_zero (fun i hi => hq i n (Nat.ne_of_lt (Finset.mem_range.mp hi)))
  have he : orthogonalPartialSum a hp hq (n+1)=patch v (a n) ho₁ ho₂ := by
    apply ext
    change (orthogonalPartialSum a hp hq (n+1)).val=v.val+(a n).val
    rw [orthogonalPartialSum_val,show v.val=∑ i ∈ Finset.range n, (a i).val from
      orthogonalPartialSum_val a hp hq n,Finset.sum_range_succ]
  rw [he]
  exact v.le_patch (a n) ho₁ ho₂

include hp hq in
/-- An actual infinite orthogonal sum, with least upper bound characterizations
for both support projections. It may be used to construct a shift. -/
theorem traceFree_orthogonal_sum :
    ∃ v : PartialIsometry M, (∀ i, a i ≤ v) ∧
      (∀ p : AlgebraProjection M, v.support ≤ p ↔ ∀ i, (a i).support ≤ p) ∧
      (∀ q : AlgebraProjection M, v.target ≤ q ↔ ∀ i, (a i).target ≤ q) := by
  obtain ⟨v,hv,hs,ht⟩ := traceFree_monotone_least_supports
    (orthogonalPartialSum a hp hq) (orthogonalPartialSum_monotone a hp hq)
  have hav (i : ℕ) : a i ≤ v :=
    (le_orthogonalPartialSum a hp hq i (i+1) (Nat.lt_succ_self i)).trans (hv (i+1))
  refine ⟨v,hav,?_,?_⟩
  · intro p
    refine ⟨fun h i => (support_mono (hav i)).trans h, fun h => hs p ?_⟩
    intro n
    change p.val*(orthogonalPartialSum a hp hq n).support.val=_
    rw [orthogonalPartialSum_support,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => h i)
  · intro q
    refine ⟨fun h i => (target_mono (hav i)).trans h, fun h => ht q ?_⟩
    intro n
    change q.val*(orthogonalPartialSum a hp hq n).target.val=_
    rw [orthogonalPartialSum_target,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => h i)

end PartialIsometry
end

/-! Projection equivalence and subequivalence are witnessed by actual partial
isometries in the original algebra. No dimension or trace oracle is used. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

/-- Link two ranges whose displayed partial isometries have the same source. -/
def rangeLink (v w : PartialIsometry M) (h : v.support=w.support) : PartialIsometry M :=
  w.compose v.adjoint (by rw [adjoint_target,h])

theorem rangeLink_target (v w : PartialIsometry M) (h : v.support=w.support) :
    (rangeLink v w h).target=w.target :=
  compose_target_of_eq w v.adjoint ((adjoint_target v).trans h)

end PartialIsometry

/-! Finiteness excludes an infinite family of nonzero equivalent orthogonal
projections. The shift and both of its least supports are constructed. -/

/-! Finite comparison and cancellation with actual partial isometries.
No trace, dimension, or representation is assumed. -/
end Tracial

/-! Actual finite sums of orthogonal partial isometries and finite subsets of
equivalent partitions. The finite subset is arbitrary, without an index order. -/
open scoped BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem subset_singleton [DecidableEq ι] (E : EquivalentPartition p ι) (i : ι) :
    E.subset {i}=(E.leg i).target := Subtype.ext (by simp only [subset_val,Finset.sum_singleton])

/-! Exact finite cardinal comparison of sums of equivalent nonzero projections.
Finiteness prevents a larger collection from embedding in a smaller one. -/

end EquivalentPartition
end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Archimedean comparison for the constructed dyadic reference projections.
Orthogonal sibling corners supply copies for the finite-algebra shift argument. -/
section
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

def traceFreeDyadicReference (p : AlgebraProjection M) (n : ℕ) : AlgebraProjection M :=
  ((traceFreeDyadicPartition hfactor hdiff p n).leg (dyadicFalseIndex n)).target

theorem traceFreeDyadic_child_le (p : AlgebraProjection M) (n : ℕ)
    (i : DyadicIndex n) (b : Bool) :
    ((traceFreeDyadicPartition hfactor hdiff p (n+1)).leg (i,b)).target ≤
      ((traceFreeDyadicPartition hfactor hdiff p n).leg i).target :=
  PartialIsometry.compose_target_le _ _ (by
    rw [EquivalentPartition.initial]
    exact EquivalentPartition.bound _ b)

end Tracial

end

/-! Finite rounding by actual subset projections. A maximal fitting subset
leaves a remainder smaller in comparison than any unused equivalent piece. -/

/-! Classification of projection comparison by the constructed finite
dimension, and a wrapper for exactly the original IsII1Factor predicate.
No normality or trace-extension claim is made here. -/

/-! Bounds and concrete dyadic upper approximants for the constructed
projection dimension. These finite estimates do not assume continuity. -/
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

/-- A subset of the n-th reference partition with weight in [c,c+2^(-n)]. -/
theorem exists_dyadicWeight_upper (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    ∃ s : Finset (DyadicIndex n), c ≤ dyadicWeight n s ∧ dyadicWeight n s ≤ c+1/2^n := by
  classical
  have hn : (0 : ℝ)<2^n := pow_pos (by norm_num) n
  have hk : Nat.ceil (c*2^n) ≤ Fintype.card (DyadicIndex n) := by
    rw [card_dyadicIndex,Nat.ceil_le]
    push_cast
    nlinarith
  obtain ⟨s,_,hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (DyadicIndex n))) (n := Nat.ceil (c*2^n))
    (by simpa only [Finset.card_univ] using hk)
  refine ⟨s,?_,?_⟩
  · change c ≤ (s.card : ℝ)/2^n
    rw [hs,le_div_iff₀ hn]
    exact Nat.le_ceil _
  · change (s.card : ℝ)/2^n ≤ c+1/2^n
    rw [hs,div_le_iff₀ hn]
    have h := (Nat.ceil_lt_add_one (mul_nonneg hc hn.le)).le
    calc (Nat.ceil (c*2^n) : ℝ) ≤ c*2^n+1 := h
         _ = (c+1/2^n)*2^n := by field_simp

include hfinite in
/-- Actual projection upper approximants for every real c in [0,1]. -/
theorem traceFreeDimension_exists_upper
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    ∃ r : AlgebraProjection M, c ≤ traceFreeDimension hfactor hdiff r ∧
      traceFreeDimension hfactor hdiff r ≤ c+1/2^n := by
  obtain ⟨s,hs,ht⟩ := exists_dyadicWeight_upper c hc hc1 n
  refine ⟨(traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n).subset s,?_,?_⟩
  · simpa only [traceFreeDimension,traceFreeDyadicSup_subset hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ hunit] using hs
  · simpa only [traceFreeDimension,traceFreeDyadicSup_subset hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ hunit] using ht

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralDimension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite spectral weights of the constructed projection dimension obey an
operator-norm bound. No linear trace on noncommuting elements is assumed. -/

/-! Construct the unique real spectral dimension value of each self-adjoint
operator by norm approximation. Global noncommuting additivity is not asserted. -/
section
open Filter
open scoped BigOperators Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

/-- Approximation specification, not an assumed linear trace. -/
def IsDimensionSpectralValue (x : M.toStarSubalgebra) (t : ℂ) : Prop :=
  ∀ (Q : CornerPartition ⟨1,IsStarProjection.one _⟩) (c : Fin Q.size → ℂ),
    (∀ i, Commute (Q.piece i).val x) →
      ‖t-∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)‖ ≤
        ‖x-∑ i, c i • (Q.piece i).val‖

theorem IsDimensionSpectralValue.unique
    {x : M.toStarSubalgebra} (hx : IsSelfAdjoint x) {s t : ℂ}
    (hs : IsDimensionSpectralValue hfactor hdiff x s)
    (ht : IsDimensionSpectralValue hfactor hdiff x t) : s=t := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply eq_of_all_dyadic_errors
  intro n
  obtain ⟨Q,c,_,hQ,herr⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ x hx (1/2^n) (by positivity)
  have hcomm := hQ x (Commute.refl x) (Commute.one_left x)
  have hs' := hs Q (fun i => (c i : ℂ)) hcomm
  have ht' := ht Q (fun i => (c i : ℂ)) hcomm
  simp only [one_mul,mul_one] at herr
  let w : ℂ := ∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)
  have htri := dist_triangle s w t
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev w t] at htri
  dsimp only [w] at htri
  have hnorm : ‖s-t‖ ≤ 2/2^n := by
    rw [show (2 : ℝ)/2^n=2*(1/2^n) by ring]
    linarith
  simpa only [sub_zero,abs_of_nonneg (norm_nonneg _)] using hnorm

end

/-! The constructed spectral value is bounded and extends the actual
projection dimension. These laws do not assert noncommuting additivity. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem IsDimensionSpectralValue.norm_le {x : M.toStarSubalgebra} {t : ℂ}
    (ht : IsDimensionSpectralValue hfactor hdiff x t) : ‖t‖ ≤ ‖x‖ := by
  have h := ht (CornerPartition.single ⟨1,IsStarProjection.one _⟩) (fun _ => 0)
    (fun _ => Commute.one_left x)
  simpa only [zero_mul,zero_smul,Finset.sum_const_zero,sub_zero] using h

theorem IsDimensionSpectralValue.on_projection (p : AlgebraProjection M) {t : ℂ}
    (ht : IsDimensionSpectralValue hfactor hdiff p.val t) :
    t=(traceFreeDimension hfactor hdiff p : ℂ) := by
  classical
  let r : AlgebraProjection M := ⟨1-p.val,p.property.one_sub⟩
  let a (b : Bool) : AlgebraProjection M := if b then r else p
  have hpr : p.val*r.val=0 := by
    change p.val*(1-p.val)=0
    rw [mul_sub,mul_one,p.property.isIdempotentElem.eq,sub_self]
  have ho (b c : Bool) (hbc : b≠c) : (a b).val*(a c).val=0 := by
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact hpr
    · exact PartialIsometry.orthogonal_reverse p r hpr
    · exact (hbc rfl).elim
  have ha : (∑ b : Bool, (a b).val)=(1 : M.toStarSubalgebra) := by
    change (∑ b : Bool, (if b then r else p).val)=1
    simp only [Fintype.sum_bool,ite_true, if_true,Bool.false_eq_true,ite_false, if_false]
    change (1-p.val)+p.val=1
    abel
  let Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) :=
    CornerPartition.ofFamily a ho ha
  let e : Fin Q.size ≃ Bool := (Fintype.equivFin Bool).symm
  let c (i : Fin Q.size) : ℂ := if e i then 0 else 1
  have hQ (i : Fin Q.size) : Commute (Q.piece i).val p.val := by
    change Commute (a (e i)).val p.val
    cases h : e i
    · exact Commute.refl p.val
    · exact (Commute.one_left p.val).sub_left (Commute.refl p.val)
  have hs : (∑ i, c i • (Q.piece i).val)=p.val := by
    change (∑ i, (if e i then (0 : ℂ) else 1) • (a (e i)).val)=p.val
    exact (Equiv.sum_comp e (fun b : Bool => (if b then (0 : ℂ) else 1) • (a b).val)).trans
      (by simp [a])
  have hw : (∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))=
      (traceFreeDimension hfactor hdiff p : ℂ) := by
    change (∑ i, (if e i then (0 : ℂ) else 1)*
      (traceFreeDimension hfactor hdiff (a (e i)) : ℂ))=_
    exact (Equiv.sum_comp e (fun b : Bool => (if b then (0 : ℂ) else 1)*
      (traceFreeDimension hfactor hdiff (a b) : ℂ))).trans (by simp [a])
  have h := ht Q c hQ
  rw [hs,sub_self,norm_zero] at h
  exact (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))).trans hw

end

/-! Finite-family tests and real homogeneity for the constructed spectral value.
These statements do not assert additivity for noncommuting operators. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem IsDimensionSpectralValue.family_bound {x : M.toStarSubalgebra} {t : ℂ}
    (ht : IsDimensionSpectralValue hfactor hdiff x t)
    {I : Type*} [Fintype I] (q : I → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0)
    (hs : ∑ i, (q i).val=(1 : M.toStarSubalgebra))
    (c : I → ℂ) (hc : ∀ i, Commute (q i).val x) :
    ‖t-∑ i, c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ ≤
      ‖x-∑ i, c i • (q i).val‖ := by
  classical
  let Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) :=
    CornerPartition.ofFamily q ho hs
  let e : Fin Q.size ≃ I := (Fintype.equivFin I).symm
  have h := ht Q (fun i => c (e i)) (fun i => hc (e i))
  change ‖t-∑ i, c (e i)*(traceFreeDimension hfactor hdiff (q (e i)) : ℂ)‖ ≤
    ‖x-∑ i, c (e i) • (q (e i)).val‖ at h
  rw [Equiv.sum_comp e (fun i => c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)),
    Equiv.sum_comp e (fun i => c i • (q i).val)] at h
  exact h

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralStates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-! A nonzero positive operator dominates a positive multiple of an actual
nonzero spectral projection. This proves faithfulness without linearity. -/
open scoped CStarAlgebra

/-! Unitary conjugacy preserves projection dimension and its constructed
spectral extension. No trace identity is assumed. -/
open scoped BigOperators
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem traceFreeDimension_unitaryConjugate (p : AlgebraProjection M)
    (u : unitary M.toStarSubalgebra) :
    traceFreeDimension hfactor hdiff (p.unitaryConjugate u)=traceFreeDimension hfactor hdiff p :=
  (traceFreeDyadicSup_equivalent hfactor hdiff ⟨1,IsStarProjection.one _⟩
    (p.equivalent_unitaryConjugate u)).symm

end

/-! The constructed scalar agrees on x*x and xx*, by an actual unitary polar
decomposition. This is a quadratic identity, not unrestricted additivity. -/
open scoped CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

attribute [local instance] OAI.Generator.Tracial.cornerValueStarOrder
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.cornerValueCStar
attribute [local instance] OAI.Generator.Tracial.cornerValueOrder
local instance cornerValuePreorder_r0456d5_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.cornerValueLE
theorem IsDimensionSpectralValue.corner_bound
    {x : M.toStarSubalgebra} {t : ℂ} (ht : IsDimensionSpectralValue hfactor hdiff x t)
    (p : AlgebraProjection M) (hpx : Commute p.val x)
    (Q : CornerPartition p) (c : Fin Q.size → ℂ) (hc : ∀ i, Commute (Q.piece i).val x) :
    ‖t-∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)‖ ≤
      ‖x-∑ i, c i • (Q.piece i).val‖ := by
  classical
  let r : AlgebraProjection M := ⟨1-p.val,p.property.one_sub⟩
  let q : Fin Q.size ⊕ Unit → AlgebraProjection M := Sum.elim Q.piece (fun _ => r)
  let d : Fin Q.size ⊕ Unit → ℂ := Sum.elim c (fun _ => 0)
  have ho (i j : Fin Q.size ⊕ Unit) (h : i≠j) : (q i).val*(q j).val=0 := by
    cases i with
    | inl i =>
      cases j with
      | inl j => exact Q.orthogonal i j (fun he => h (congrArg Sum.inl he))
      | inr j =>
        change (Q.piece i).val*(1-p.val)=0
        rw [mul_sub,mul_one,projection_mul_of_le (Q.piece_le i),sub_self]
    | inr i =>
      cases j with
      | inl j =>
        change (1-p.val)*(Q.piece j).val=0
        rw [sub_mul,one_mul,show p.val*(Q.piece j).val=(Q.piece j).val from Q.piece_le j,sub_self]
      | inr j => exact (h (congrArg Sum.inr (Subsingleton.elim i j))).elim
  have hs : (∑ i, (q i).val)=(1 : M.toStarSubalgebra) := by
    simp only [q,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.sum_unique,Q.total]
    change p.val+(1-p.val)=1
    abel
  have hqc (i : Fin Q.size ⊕ Unit) : Commute (q i).val x := by
    cases i with
    | inl i => exact hc i
    | inr i => exact (Commute.one_left x).sub_left hpx
  have hh := ht.family_bound hfactor hdiff q ho hs d hqc
  simpa only [q,d,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,zero_mul,zero_smul,
    Finset.sum_const_zero,add_zero] using hh

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
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

/-- Change the common initial corner by a displayed equivalence. -/
def rebase (E : EquivalentPartition p ι) (v : PartialIsometry M) (hv : v.target=E.base) :
    EquivalentPartition p ι where
  base := v.support
  leg i := (E.leg i).compose v (by rw [hv,E.initial])
  initial _ := rfl
  cross i j hij := by
    change star ((E.leg i).val*v.val)*((E.leg j).val*v.val)=0
    calc _ = star v.val*(star (E.leg i).val*(E.leg j).val)*v.val := by
           simp only [star_mul,mul_assoc]
         _ = 0 := by rw [E.cross i j hij,mul_zero,zero_mul]
  total := by simpa only [E.compose_base_target v hv] using E.total
  bound i := by rw [E.compose_base_target v hv]; exact E.bound i

end EquivalentPartition

end

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
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertCoefficientMeasurable
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurability from countably many Hilbert coefficients

The coefficients against a countable dense family give a continuous
injection into a countable product of copies of `ℂ`. Lusin–Souslin makes
this map a measurable embedding. Thus measurability of the coefficients
implies strong measurability, without assuming a Pettis theorem.
-/

namespace KadisonKastler

open MeasureTheory Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {D H ι : Type*} [MeasurableSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H] {μ : Measure D}

/-- Countably many dense coefficient tests determine a measurable vector field. -/
theorem aestronglyMeasurable_of_dense_inner [Countable ι]
    (v : ι → H) (hv : DenseRange v) (f : D → H)
    (hf : ∀ i, AEStronglyMeasurable (fun x => inner ℂ (v i) (f x)) μ) :
    AEStronglyMeasurable f μ := by
  borelize H
  let T : H → (ι → ℂ) := fun ξ i => inner ℂ (v i) ξ
  have hT : Continuous T := continuous_pi fun i => continuous_const.inner continuous_id
  have hTi : Function.Injective T := by
    intro ξ η heq
    exact hv.eq_of_inner_right ℂ (fun i => congrFun heq i)
  have hTe : MeasurableEmbedding T := hT.measurableEmbedding hTi
  have hm : AEMeasurable (T ∘ f) μ :=
    AEMeasurable.of_eval fun i => (hf i).aemeasurable
  exact (hTe.aemeasurable_comp_iff.mp hm).aestronglyMeasurable

/-- In a separable Hilbert space, measurable scalar coefficients imply
strong measurability of the vector field. -/
theorem aestronglyMeasurable_of_inner (f : D → H)
    (hf : ∀ η : H, AEStronglyMeasurable (fun x => inner ℂ η (f x)) μ) :
    AEStronglyMeasurable f μ := by
  obtain ⟨v, hv⟩ := exists_dense_seq (α := H)
  exact aestronglyMeasurable_of_dense_inner v hv f (fun n => hf (v n))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedTypeIInjectivity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The published injectivity input for type I factors

Blackadar, *Operator Algebras* (Springer, 2006), Corollary IV.2.2.10,
states that every type I von Neumann algebra is injective. Proposition
IV.2.1.4(iii) expresses this by a contractive projection in every faithful
representation. We retain only the factor case in its given representation.

The projection-theoretic hypothesis below is the usual characterization:
a factor is type I precisely when it has a nonzero minimal projection.
See III.1.3.10 and III.1.5.2--3. The latter also give the familiar spatial
form `B(H₁) ⊗ 1`. No perturbation or stability assertion is assumed.

Primary author PDF: https://bruceblackadar.com/Mathematics/Cycr.pdf
(printed pp. 244, 247, 373, 377).
-/

namespace KadisonKastler

open Generator.Tracial

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A nonzero projection with no proper nonzero subprojection in the
algebra. The order is the existing order on algebra projections. -/
def IsMinimalProjectionIn (M : VonNeumannAlgebra H) (p : AlgebraProjection M) : Prop :=
  p.val ≠ 0 ∧ ∀ q : AlgebraProjection M, q ≤ p → q.val = 0 ∨ q = p

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioParameters
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two fixed product-state parameters

The manuscript uses `exp (-1)` and `exp (-sqrt 2)`. Their logarithms
generate an incommensurable pair of modular frequencies. No parameter
depends on an algebra, representation, or requested perturbation bound.
-/

namespace KadisonKastler

noncomputable section

theorem fixedProductLambda_pos : 0 < fixedProductLambda := Real.exp_pos _

theorem fixedProductMu_pos : 0 < fixedProductMu := Real.exp_pos _

end

end KadisonKastler

end OAI
end


