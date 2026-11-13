-- Prove2me | Definitions.Def_Q260K016
-- name    : Q260K016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T05:13:39.174069+00:00
-- url     : https://prove2.me/theorems/1f239824-f464-4ccd-991b-1cc369960266
-- title:
--   Definitions bundle Q260K016 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 2 definitions and 22 theorems. The definitions and types are `OAI.Generator.Tracial.traceFreeTrace`, `OAI.KadisonKastler.ScalarOperatorKernel.reconstructedRepresentative`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_Dimension`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/Dimension.lean), [`FactorGeneration_LocalizedStates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/LocalizedStates.lean), [`FactorGeneration_NormalDimension`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/NormalDimension.lean), [`FactorGeneration_NormalTrace`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/NormalTrace.lean), [`KadisonKastler_HilbertCoefficientMeasurable`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/HilbertCoefficientMeasurable.lean), [`KadisonKastler_KernelReconstruction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/KernelReconstruction.lean), [`KadisonKastler_ScalarBoundaryMean`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ScalarBoundaryMean.lean).
--
--   **Imports.** It imports the bundle `Q260K056` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K022`, `Q260K025` and `Q260K057`; the statements `OAI_KadisonKastler_centralPairDecomposition_of_rankModel`, `OAI_KadisonKastler_commonRankOperatorField_action`, `OAI_KadisonKastler_commonRank_algebra_decompose`, `OAI_KadisonKastler_commonRank_commutant_decompose` and `OAI_KadisonKastler_quadratic_cochain_of_asymptotic_rows`; the proofs of `OAI.KadisonKastler.PreservesJordan.multiplicative_of_close_of_II1`, `OAI_KadisonKastler_commonRankOperatorField_action`, `OAI_KadisonKastler_commonRank_algebra_decompose`, `OAI_KadisonKastler_commonRank_commutant_decompose` and `OAI_KadisonKastler_quadratic_cochain_of_asymptotic_rows`.
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
import Mathlib.MeasureTheory.Measure.Prod
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
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K056

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

theorem traceFreeDyadicSup_eq_zero_iff
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p q : AlgebraProjection M) (hp : p.val≠0) :
    traceFreeDyadicSup hfactor hdiff p q=0 ↔ q.val=0 := by
  constructor
  · intro h
    by_contra hq
    have hh := traceFreeDyadicSup_pos hfactor hdiff hfinite p q hq
    rw [h] at hh
    exact lt_irrefl _ hh
  · exact traceFreeDyadicSup_zero hfactor hdiff p q hp

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
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDyadicSup_eq_iff_equivalent
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p) (hrp : r ≤ p) :
    traceFreeDyadicSup hfactor hdiff p q=traceFreeDyadicSup hfactor hdiff p r ↔
      q.Equivalent r := by
  constructor
  · intro h
    exact AlgebraProjection.equivalent_of_mutual_subequivalent hfinite
      ((traceFreeDyadicSup_le_iff_subequivalent hfactor hdiff hfinite p q r hp hqp).mp (le_of_eq h))
      ((traceFreeDyadicSup_le_iff_subequivalent hfactor hdiff hfinite p r q hp hrp).mp (le_of_eq h.symm))
  · exact traceFreeDyadicSup_equivalent hfactor hdiff p

end Tracial

end

/-! Bounds and concrete dyadic upper approximants for the constructed
projection dimension. These finite estimates do not assume continuity. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_NormalDimension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Increasing projection suprema and compatible sequential comparison.
The witnesses live in the original algebra; no trace or dimension is used. -/

/-! Original-factor wrapper for normalized faithful order-continuous projection
dimension. This does not assert the existence of a linear trace functional. -/

/-! Exact prescribed dimensions are attained by actual subprojections.
Chain bounds use the proved arbitrary-net continuity of dimension. -/
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_exists_small_subprojection
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (p : AlgebraProjection M) (hp : p.val≠0) (ε : ℝ) (hε : 0<ε) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ 0 < traceFreeDimension hfactor hdiff q ∧
      traceFreeDimension hfactor hdiff q < ε := by
  classical
  have hpD : 0 < traceFreeDimension hfactor hdiff p :=
    traceFreeDyadicSup_pos hfactor hdiff hfinite _ p hp
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (lt_min hε hpD) (by norm_num : (1/2 : ℝ)<1)
  rw [one_div_pow] at hn
  have hn0 : (0 : ℝ)<1/2^n := by positivity
  have hi : Nonempty (DyadicIndex n) := Fintype.card_pos_iff.mp (by
    rw [card_dyadicIndex]; positivity)
  let i : DyadicIndex n := Classical.choice hi
  let e := (traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n).subset {i}
  have heD : traceFreeDimension hfactor hdiff e=1/2^n := by
    change traceFreeDyadicSup hfactor hdiff ⟨1,IsStarProjection.one _⟩
      ((traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n).subset {i})=1/2^n
    rw [traceFreeDyadicSup_subset hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩ hunit]
    simp only [dyadicWeight,Finset.card_singleton,Nat.cast_one]
  obtain ⟨v,hv,ht⟩ := (traceFreeDimension_le_iff_subequivalent hfactor hdiff hfinite hunit e p).mp
    (by rw [heD]; exact (lt_min_iff.mp hn).2.le)
  have he : traceFreeDimension hfactor hdiff v.target=1/2^n := by
    have h := traceFreeDyadicSup_equivalent hfactor hdiff ⟨1,IsStarProjection.one _⟩
      (show e.Equivalent v.target from ⟨v,hv,rfl⟩)
    exact h.symm.trans heD
  exact ⟨v.target,ht,by rw [he]; exact hn0,by rw [he]; exact (lt_min_iff.mp hn).1⟩

include hfinite in
theorem traceFreeDimension_bounded_chain
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : Set (AlgebraProjection M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (p : AlgebraProjection M) (d : ℝ)
    (hp : ∀ q ∈ c, q ≤ p) (hd : ∀ q ∈ c, traceFreeDimension hfactor hdiff q ≤ d) :
    ∃ q : AlgebraProjection M, (∀ r ∈ c, r ≤ q) ∧ q ≤ p ∧
      traceFreeDimension hfactor hdiff q ≤ d := by
  let : Nonempty c := hne.to_subtype
  let : IsDirected c (· ≤ ·) := ⟨by
    intro u v
    rcases hc.total u.property v.property with h | h
    · exact ⟨v,h,le_rfl⟩
    · exact ⟨u,le_rfl,h⟩⟩
  obtain ⟨q,hq,hD⟩ := traceFreeDimension_exists_isLUB hfactor hdiff hfinite hunit
    (fun r : c => r.val) (fun _ _ h => h)
  refine ⟨q,fun r hr => hq.1 ⟨⟨r,hr⟩,rfl⟩,?_,?_⟩
  · exact hq.2 (by rintro _ ⟨r,rfl⟩; exact hp r.val r.property)
  · rw [hD]
    exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨r,rfl⟩; exact hd r.val r.property)

include hfinite in
theorem traceFreeDimension_exists_maximal_below
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (p : AlgebraProjection M) (d : ℝ) (hd : 0 ≤ d) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ traceFreeDimension hfactor hdiff q ≤ d ∧
      ∀ r : AlgebraProjection M, r ≤ p → traceFreeDimension hfactor hdiff r ≤ d →
        q ≤ r → r ≤ q := by
  let S : Set (AlgebraProjection M) := {q | q ≤ p ∧ traceFreeDimension hfactor hdiff q ≤ d}
  obtain ⟨q,hq⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · obtain ⟨q,hcq,hqp,hqd⟩ := traceFreeDimension_bounded_chain hfactor hdiff hfinite hunit
        c hchain hne p d (fun q hq => (hc hq).1) (fun q hq => (hc hq).2)
      exact ⟨q,⟨hqp,hqd⟩,hcq⟩
    · refine ⟨⟨0,IsStarProjection.zero _⟩,⟨mul_zero _,?_⟩,?_⟩
      · have hz := traceFreeDyadicSup_zero hfactor hdiff ⟨1,IsStarProjection.one _⟩
          ⟨0,IsStarProjection.zero _⟩ hunit rfl
        exact hz.le.trans hd
      · intro r hr
        exact (hne ⟨r,hr⟩).elim)
  exact ⟨q,hq.1.1,hq.1.2,fun r hr hrd hqr => hq.2 ⟨hr,hrd⟩ hqr⟩

include hfinite in
/-- Every dimension between zero and D(p) is realized inside p. -/
theorem traceFreeDimension_exists_subprojection
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (p : AlgebraProjection M) (d : ℝ) (hd : 0 ≤ d)
    (hdp : d ≤ traceFreeDimension hfactor hdiff p) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ traceFreeDimension hfactor hdiff q=d := by
  obtain ⟨q,hqp,hqd,hmax⟩ := traceFreeDimension_exists_maximal_below
    hfactor hdiff hfinite hunit p d hd
  refine ⟨q,hqp,le_antisymm hqd ?_⟩
  by_contra hnot
  have hlt : traceFreeDimension hfactor hdiff q < d := lt_of_not_ge hnot
  let r := AlgebraProjection.remainder q p hqp
  have hr : r.val≠0 := by
    change p.val-q.val≠0
    intro hz
    have he : p=q := Subtype.ext (sub_eq_zero.mp hz)
    rw [he] at hdp
    exact (not_lt_of_ge hdp) hlt
  obtain ⟨s,hs,hpos,hsmall⟩ := traceFreeDimension_exists_small_subprojection
    hfactor hdiff hfinite hunit r hr (d-traceFreeDimension hfactor hdiff q) (sub_pos.mpr hlt)
  have ho : q.val*s.val=0 :=
    projection_orthogonal_of_le (AlgebraProjection.remainder_orthogonal q p hqp) le_rfl hs
  let t := orthogonalSum q s ho
  have htp : t ≤ p := orthogonalSum_le ho hqp (hs.trans (AlgebraProjection.remainder_le q p hqp))
  have htD : traceFreeDimension hfactor hdiff t=
      traceFreeDimension hfactor hdiff q+traceFreeDimension hfactor hdiff s :=
    traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩ q s
      hunit (one_mul _) (one_mul _) ho
  have htd : traceFreeDimension hfactor hdiff t ≤ d := by rw [htD]; linarith
  have hle : t ≤ q := hmax t htp htd (le_orthogonalSum_left _ _ ho)
  have hmono := traceFreeDimension_mono hfactor hdiff hle
  rw [htD] at hmono
  linarith

end

/-! Finite partitions with prescribed dimensions, and actual equivalent
partitions of arbitrary positive finite size in every corner. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_remainder
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (q p : AlgebraProjection M) (hq : q ≤ p) :
    traceFreeDimension hfactor hdiff (AlgebraProjection.remainder q p hq)=
      traceFreeDimension hfactor hdiff p-traceFreeDimension hfactor hdiff q := by
  have h := traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite
    ⟨1,IsStarProjection.one _⟩ q (AlgebraProjection.remainder q p hq)
    hunit (one_mul _) (one_mul _) (AlgebraProjection.remainder_orthogonal q p hq)
  rw [AlgebraProjection.orthogonalSum_remainder] at h
  change traceFreeDimension hfactor hdiff p=
    traceFreeDimension hfactor hdiff q+
      traceFreeDimension hfactor hdiff (AlgebraProjection.remainder q p hq) at h
  linarith

include hfinite in
/-- Every prescribed finite list of nonnegative dimensions summing to D(p)
is realized by pairwise orthogonal actual projections summing to p. -/
theorem traceFreeDimension_exists_partition
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (n : ℕ) (p : AlgebraProjection M) (d : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hsum : ∑ i, d i=traceFreeDimension hfactor hdiff p) :
    ∃ q : Fin n → AlgebraProjection M, (∀ i, q i ≤ p) ∧
      (∀ i j, i≠j → (q i).val*(q j).val=0) ∧
      (∑ i, (q i).val)=p.val ∧ (∀ i, traceFreeDimension hfactor hdiff (q i)=d i) := by
  induction n generalizing p with
  | zero =>
    have hpD : traceFreeDimension hfactor hdiff p=0 := by simpa using hsum.symm
    have hpz : p.val=0 := (traceFreeDyadicSup_eq_zero_iff hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ p hunit).mp hpD
    refine ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i,fun i => Fin.elim0 i,?_,fun i => Fin.elim0 i⟩
    simpa using hpz.symm
  | succ n ih =>
    have hsum' : d 0+∑ i : Fin n, d i.succ=traceFreeDimension hfactor hdiff p := by
      simpa only [Fin.sum_univ_succ] using hsum
    have hdp : d 0 ≤ traceFreeDimension hfactor hdiff p := by
      have hh : 0 ≤ ∑ i : Fin n, d i.succ := Finset.sum_nonneg (fun i _ => hd i.succ)
      linarith
    obtain ⟨q,hqp,hqd⟩ := traceFreeDimension_exists_subprojection
      hfactor hdiff hfinite hunit p (d 0) (hd 0) hdp
    let r := AlgebraProjection.remainder q p hqp
    have hrD : traceFreeDimension hfactor hdiff r=
        traceFreeDimension hfactor hdiff p-d 0 := by
      rw [traceFreeDimension_remainder hfactor hdiff hfinite hunit q p hqp,hqd]
    obtain ⟨b,hbr,hbo,hbs,hbd⟩ := ih r (fun i => d i.succ) (fun i => hd i.succ) (by
      rw [hrD]; linarith)
    let a : Fin (n+1) → AlgebraProjection M := Fin.cons q b
    have hqb (i : Fin n) : q.val*(b i).val=0 :=
      projection_orthogonal_of_le (AlgebraProjection.remainder_orthogonal q p hqp) le_rfl (hbr i)
    refine ⟨a,?_,?_,?_,?_⟩
    · intro i
      refine Fin.cases hqp (fun j => ?_) i
      exact (hbr j).trans (AlgebraProjection.remainder_le q p hqp)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro k
        refine Fin.cases ?_ (fun l => ?_) k
        · intro h; exact (h rfl).elim
        · intro _; exact hqb l
      · intro k
        refine Fin.cases ?_ (fun l => ?_) k
        · intro _; exact PartialIsometry.orthogonal_reverse q (b j) (hqb j)
        · intro h
          exact hbo j l (fun he => h (congrArg Fin.succ he))
    · rw [Fin.sum_univ_succ]
      change q.val+(∑ i, (b i).val)=p.val
      rw [hbs]
      change q.val+(p.val-q.val)=p.val
      abel
    · intro i
      exact Fin.cases hqd hbd i

include hfinite in
/-- A finite corner partition into n equal dimensions, for every n>0. -/
theorem traceFreeDimension_exists_uniform_partition
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (n : ℕ) (hn : 0<n) (p : AlgebraProjection M) :
    ∃ q : Fin n → AlgebraProjection M, (∀ i, q i ≤ p) ∧
      (∀ i j, i≠j → (q i).val*(q j).val=0) ∧
      (∑ i, (q i).val)=p.val ∧
      (∀ i, traceFreeDimension hfactor hdiff (q i)=traceFreeDimension hfactor hdiff p/n) := by
  apply traceFreeDimension_exists_partition hfactor hdiff hfinite hunit n p
    (fun _ => traceFreeDimension hfactor hdiff p/n)
  · intro i
    exact div_nonneg (traceFreeDimension_nonneg hfactor hdiff p) (Nat.cast_nonneg n)
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp

include hfactor hdiff hfinite in
/-- Actual matrix-unit legs for a partition of every positive finite size. -/
theorem traceFreeDimension_exists_equivalent_partition
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (n : ℕ) (hn : 0<n) (p : AlgebraProjection M) :
    Nonempty (EquivalentPartition p (Fin n)) := by
  classical
  obtain ⟨q,hqp,hqo,hqs,hqd⟩ := traceFreeDimension_exists_uniform_partition
    hfactor hdiff hfinite hunit n hn p
  let i₀ : Fin n := ⟨0,hn⟩
  have he (i : Fin n) : (q i₀).Equivalent (q i) :=
    (traceFreeDyadicSup_eq_iff_equivalent hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩
      (q i₀) (q i) hunit (one_mul _) (one_mul _)).mp ((hqd i₀).trans (hqd i).symm)
  choose v hv ht using he
  exact ⟨{
    base := q i₀
    leg := v
    initial := hv
    cross := fun i j hij => (v i).adjoint.mul_eq_zero (v j) (by
      change (v i).target.val*(v j).target.val=0
      rw [ht i,ht j]; exact hqo i j hij)
    total := by simpa only [ht] using hqs
    bound := fun i => by rw [ht]; exact hqp i }⟩

end Tracial

/-! Actual vector functionals and their continuity on directed projection
suprema. No factor, trace, separability, or dimension hypothesis is used. -/
open Filter
open scoped Topology BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-! Projection localization yields actual positive-operator inequalities for
bounded linear functionals, and a nearly cyclic functional on the corner. -/
open scoped BigOperators CStarAlgebra

/-! An actual positive normalized vector functional with arbitrarily small
multiplicative failure of cyclicity on a nonzero corner. No trace is assumed. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.cornerStateStarOrder
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.cornerStateCStar
attribute [local instance] OAI.Generator.Tracial.cornerStateOrder
local instance cornerStatePreorder_r3b06b9_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.cornerStateLE
include hfactor hdiff hfinite in
/-- A localized vector functional is nearly cyclic for every element in its
corner. This gives both inequalities by applying the result to x and x*. -/
theorem exists_corner_nearly_cyclic_vector
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (hξ : ‖ξ‖=1) (ε : ℝ) (hε : 0<ε) :
    ∃ E : AlgebraProjection M, E.val≠0 ∧
      (∀ p : AlgebraProjection M, p ≤ E → p.val≠0 → 0<(vectorFunctional ξ p.val).re) ∧
      ∀ x : M.toStarSubalgebra, E.val*x=x → x*E.val=x →
        (vectorFunctional ξ (star x*x)).re ≤ (1+ε)*(vectorFunctional ξ (x*star x)).re := by
  obtain ⟨E,a,hE,ha,h⟩ := exists_localized_vector_functional
    hfactor hdiff hfinite hunit ξ hξ ε hε
  refine ⟨E,hE,?_,?_⟩
  · intro p hp hpn
    have hpstar : star p.val*p.val=p.val := by
      rw [p.property.isSelfAdjoint.star_eq,p.property.isIdempotentElem.eq]
    have hpnonneg : 0 ≤ p.val := hpstar ▸ star_mul_self_nonneg p.val
    have hh := (h p.val hpnonneg hp).1
    rw [dimensionSpectralValue_projection,Complex.ofReal_re] at hh
    exact (mul_pos ha (traceFreeDyadicSup_pos hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ p hpn)).trans_le hh
  intro x hEx hxE
  have hExs : E.val*star x=star x := by
    simpa only [star_mul,E.property.isSelfAdjoint.star_eq] using congrArg star hxE
  have h₁ := h (star x*x) (star_mul_self_nonneg x) (by rw [← mul_assoc,hExs])
  have h₂ := h (x*star x) (mul_star_self_nonneg x) (by rw [← mul_assoc,hEx])
  have he := congrArg Complex.re (dimensionSpectralValue_star_mul_self hfactor hdiff hfinite hunit x)
  have hm := mul_le_mul_of_nonneg_left h₂.1 (by linarith : 0 ≤ 1+ε)
  rw [← he] at hm
  nlinarith [h₁.2]

end

/-! A full finite matrix partition can be rebased into every nonzero corner.
The legs are constructed partial isometries, not assumed matrix units. -/
open scoped BigOperators
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hdiff hfinite in
/-- A partition of 1 with common initial projection inside any given nonzero E. -/
theorem exists_equivalent_partition_base_le
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (E : AlgebraProjection M) (hE : E.val≠0) :
    ∃ (n : ℕ) (_hn : 0<n)
      (Q : EquivalentPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) (Fin n)),
      Q.base ≤ E ∧ Q.base.val≠0 := by
  have hD : 0<traceFreeDimension hfactor hdiff E :=
    traceFreeDyadicSup_pos hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩ E hE
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hD (by norm_num : (1/2 : ℝ)<1)
  rw [one_div_pow] at hn
  have hn0 : 0<2^n := Nat.two_pow_pos n
  let Q := Classical.choice (traceFreeDimension_exists_equivalent_partition
    hfactor hdiff hfinite hunit (2^n) hn0 ⟨1,IsStarProjection.one _⟩)
  have : Nonempty (Fin (2^n)) := ⟨⟨0,hn0⟩⟩
  have hQ : traceFreeDimension hfactor hdiff Q.base=1/2^n := by
    rw [Q.dimension_base hfactor hdiff hfinite hunit]
    have h1 : traceFreeDimension hfactor hdiff (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M)=1 :=
      traceFreeDyadicSup_self hfactor hdiff ⟨1,IsStarProjection.one _⟩
    rw [h1]
    simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  obtain ⟨v,hv,ht⟩ := (traceFreeDimension_le_iff_subequivalent hfactor hdiff hfinite hunit Q.base E).mp
    (by rw [hQ]; exact hn.le)
  have hvt : v.adjoint.target=Q.base := by
    apply Subtype.ext
    change star v.val*star (star v.val)=Q.base.val
    rw [star_star,v.initial,hv]
  let R := Q.rebase v.adjoint hvt
  exact ⟨2^n,hn0,R,ht,R.base_ne_zero hunit⟩

end

/-! Extension of a vector functional through actual matrix-partition legs.
Finite coefficient identities transfer the corner quadratic inequality. -/
open scoped BigOperators CStarAlgebra

/-! Globally defined positive unital linear functionals with arbitrarily small multiplicative quadratic trace error. -/
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.approxTraceCStar
local instance approxTraceOrder_r3b06b9_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance approxTracePreorder_r3b06b9_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.approxTraceLE
local instance approxTraceStarOrder_r3b06b9_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hdiff hfinite in
/-- A constructed approximate tracial state on the entire original algebra. -/
theorem exists_approximately_tracial_state
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (ε : ℝ) (hε : 0<ε) :
    ∃ φ : M.toStarSubalgebra →L[ℂ] ℂ,
      ‖φ‖ ≤ 1 ∧ φ 1=1 ∧ (∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re) ∧
      ∀ x : M.toStarSubalgebra, (φ (star x*x)).re ≤ (1+ε)*(φ (x*star x)).re := by
  classical
  obtain ⟨ξ,hξ⟩ := exists_unit_vector_of_unit_ne_zero hunit
  obtain ⟨E,hE,hfaith,hcorner⟩ := exists_corner_nearly_cyclic_vector
    hfactor hdiff hfinite hunit ξ hξ ε hε
  obtain ⟨n,hn,Q,hQE,hQ⟩ := exists_equivalent_partition_base_le hfactor hdiff hfinite hunit E hE
  have hbase : 0<(vectorFunctional ξ Q.base.val).re := hfaith Q.base hQE hQ
  let A : ℝ := ∑ i, ‖(Q.leg i).val.val ξ‖^2
  have hi (i : Fin n) : ‖(Q.leg i).val.val ξ‖^2=(vectorFunctional ξ Q.base.val).re := by
    have h := congrArg Complex.re (vectorFunctional_star_mul_self ξ (Q.leg i).val)
    rw [(Q.leg i).initial,Q.initial] at h
    exact_mod_cast h.symm
  have hA : 0<A := by
    apply Finset.sum_pos
    · intro i _
      rw [hi]
      exact hbase
    · exact ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  let F := Q.matrixVectorFunctional ξ
  have hF1 : F 1=(A : ℂ) := Q.matrixVectorFunctional_one ξ
  have hFnorm : ‖F‖ ≤ A := Q.matrixVectorFunctional_norm_le ξ
  have hFpos (x : M.toStarSubalgebra) (hx : 0 ≤ x) : 0 ≤ (F x).re := by
    change 0 ≤ ((∑ i, vectorFunctional ((Q.leg i).val.val ξ)) x).re
    rw [sum_apply,Complex.re_sum]
    exact Finset.sum_nonneg (fun i _ => vectorFunctional_positive _ x hx)
  have hFtrace (x : M.toStarSubalgebra) : (F (star x*x)).re ≤ (1+ε)*(F (x*star x)).re := by
    apply Q.matrixVectorFunctional_nearly_cyclic rfl ξ ε ?_ x
    intro y hly hry
    have hl : E.val*y=y := by
      calc E.val*y = E.val*(Q.base.val*y) := by rw [hly]
           _ = y := by rw [← mul_assoc,show E.val*Q.base.val=Q.base.val from hQE,hly]
    have hr : y*E.val=y := by
      calc y*E.val = (y*Q.base.val)*E.val := by rw [hry]
           _ = y := by rw [mul_assoc,projection_mul_of_le hQE,hry]
    exact hcorner y hl hr
  let φ : M.toStarSubalgebra →L[ℂ] ℂ := ((A⁻¹ : ℝ) : ℂ) • F
  have hφ (x : M.toStarSubalgebra) : (φ x).re=A⁻¹*(F x).re := by
    simp only [φ,smul_apply,smul_eq_mul,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  refine ⟨φ,?_,?_,?_,?_⟩
  · change ‖((A⁻¹ : ℝ) : ℂ) • F‖ ≤ 1
    rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hA.le)]
    exact (mul_le_mul_of_nonneg_left hFnorm (inv_nonneg.mpr hA.le)).trans_eq (inv_mul_cancel₀ hA.ne')
  · change ((A⁻¹ : ℝ) : ℂ)*(F 1)=1
    rw [hF1,← Complex.ofReal_mul,inv_mul_cancel₀ hA.ne',Complex.ofReal_one]
  · intro x hx
    rw [hφ]
    exact mul_nonneg (inv_nonneg.mpr hA.le) (hFpos x hx)
  · intro x
    rw [hφ,hφ]
    have h := mul_le_mul_of_nonneg_left (hFtrace x) (inv_nonneg.mpr hA.le)
    calc A⁻¹*(F (star x*x)).re ≤ A⁻¹*((1+ε)*(F (x*star x)).re) := h
         _ = (1+ε)*(A⁻¹*(F (x*star x)).re) := by ring

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/
section
open Filter
open scoped Topology CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.quadraticStateCStar
local instance quadraticStateOrder_r3b06b9_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance quadraticStatePreorder_r3b06b9_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.quadraticStateLE
local instance quadraticStateStarOrder_r3b06b9_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hdiff hfinite in
theorem exists_real_quadratic_state (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    ∃ φ : M.toStarSubalgebra →L[ℂ] ℂ,
      ‖φ‖ ≤ 1 ∧ φ 1=1 ∧ (∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re) ∧
      ∀ x : M.toStarSubalgebra, (φ (star x*x)).re=(φ (x*star x)).re := by
  have hex (n : ℕ) := exists_approximately_tracial_state hfactor hdiff hfinite hunit
    (1/((n : ℝ)+1)) (by positivity)
  choose f hf hfone hfpos hfquad using hex
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  obtain ⟨φ,hφ,ht⟩ := exists_bounded_functional_ultralimit ω f 1 (by norm_num) hf
  have hε : Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) (ω : Filter ℕ) (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left (Ultrafilter.of_le _)
  have hre (x : M.toStarSubalgebra) := (Complex.continuous_re.tendsto (φ x)).comp (ht x)
  have hle (x : M.toStarSubalgebra) : (φ (star x*x)).re ≤ (φ (x*star x)).re := by
    have hr := (hε.const_add 1).mul (hre (x*star x))
    have h := le_of_tendsto_of_tendsto (hre (star x*x)) hr
      (Eventually.of_forall (fun n => hfquad n x))
    simpa only [add_zero,one_mul] using h
  refine ⟨φ,hφ,?_,?_,?_⟩
  · apply tendsto_nhds_unique (ht 1)
    simpa only [hfone] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) (ω : Filter ℕ) (𝓝 1))
  · intro x hx
    exact ge_of_tendsto (hre x) (Eventually.of_forall (fun n => hfpos n x hx))
  · intro x
    exact le_antisymm (hle x) (by simpa only [star_star] using hle (star x))

end

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/
section
open scoped CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.tracialStateStarOrder
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.tracialStateCStar
attribute [local instance] OAI.Generator.Tracial.tracialStateOrder
local instance tracialStatePreorder_r3b06b9_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.tracialStateLE
include hfactor hdiff hfinite in
theorem exists_tracial_state (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    ∃ φ : M.toStarSubalgebra →L[ℂ] ℂ,
      ‖φ‖ ≤ 1 ∧ φ 1=1 ∧ (∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re) ∧
      (∀ x : M.toStarSubalgebra, φ (star x)=star (φ x)) ∧
      ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x) := by
  obtain ⟨φ,hφ,h1,hpos,hquad⟩ := exists_real_quadratic_state hfactor hdiff hfinite hunit
  refine ⟨hermitianFunctional φ,(hermitianFunctional_norm_le φ).trans hφ,
    hermitianFunctional_one φ h1,?_,hermitianFunctional_star φ,
    hermitianFunctional_trace φ hquad⟩
  intro x hx
  rw [hermitianFunctional_selfAdjoint φ x hx.isSelfAdjoint,Complex.ofReal_re]
  exact hpos x hx

end

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/
section
open Filter
open scoped Topology CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.traceStarOrder
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

attribute [local instance] OAI.Generator.Tracial.traceCStar
attribute [local instance] OAI.Generator.Tracial.traceLE
def traceFreeTrace : M.toStarSubalgebra →L[ℂ] ℂ :=
  (exists_tracial_state hfactor hdiff hfinite hunit).choose

end

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
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertCoefficientMeasurable
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Once a field has measurable evaluations, its adjoint does too.
This uses the scalar adjoint identity and the preceding coefficient test. -/
theorem operator_adjoint_eval_aestronglyMeasurable
    (T : D → H →L[ℂ] H)
    (hT : ∀ ξ, AEStronglyMeasurable (fun x => T x ξ) μ) (η : H) :
    AEStronglyMeasurable (fun x => star (T x) η) μ := by
  apply aestronglyMeasurable_of_inner
  intro ξ
  simpa only [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right] using (hT ξ).inner_const (c := η)

/-- Testing both variables only on a countable dense family suffices to
make every evaluation of an operator field strongly measurable. -/
theorem operator_eval_aestronglyMeasurable_of_dense_coefficients [Countable ι]
    (v : ι → H) (hv : DenseRange v) (T : D → H →L[ℂ] H)
    (hT : ∀ i j, AEStronglyMeasurable (fun x => inner ℂ (v i) (T x (v j))) μ)
    (ξ : H) : AEStronglyMeasurable (fun x => T x ξ) μ := by
  apply aestronglyMeasurable_of_dense_inner v hv
  intro i
  obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.mp (hv ξ)
  choose j hj using hw
  have hvlim : Tendsto (fun n => v (j n)) atTop (𝓝 ξ) := by
    simpa only [hj] using hlim
  apply aestronglyMeasurable_of_tendsto_ae atTop (fun n => hT i (j n))
  exact Eventually.of_forall fun x =>
    ((continuous_const.inner (T x).continuous).tendsto ξ).comp hvlim

/-- The two sets of measurable evaluations needed for the weak operator
field C-star algebra follow from the same countable coefficient data. -/
theorem operator_field_aestronglyMeasurable_of_dense_coefficients [Countable ι]
    (v : ι → H) (hv : DenseRange v) (T : D → H →L[ℂ] H)
    (hT : ∀ i j, AEStronglyMeasurable (fun x => inner ℂ (v i) (T x (v j))) μ) :
    ∀ ξ, AEStronglyMeasurable (fun x => T x ξ) μ ∧
      AEStronglyMeasurable (fun x => star (T x) ξ) μ := by
  have hm := operator_eval_aestronglyMeasurable_of_dense_coefficients v hv T hT
  exact fun ξ => ⟨hm ξ, operator_adjoint_eval_aestronglyMeasurable T hm ξ⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarBoundaryMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem scalarInfinityConst_ae (z : ℂ) :
    scalarInfinityConst μ z =ᵐ[μ] fun _ => z := MemLp.coeFn_toLp _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_KernelReconstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable [SeparableSpace H]

/-- The resulting field and its adjoint have all strongly measurable evaluations. -/
theorem reconstructedOperator_measurable :
    ∀ ξ : H, AEStronglyMeasurable (fun x => K.reconstructedOperator C x ξ) μ ∧
      AEStronglyMeasurable (fun x => star (K.reconstructedOperator C x) ξ) μ := by
  let : Countable C.space := C.countable
  have hd : DenseRange ((↑) : C.space → H) := C.dense.denseRange_val
  apply operator_field_aestronglyMeasurable_of_dense_coefficients
    ((↑) : C.space → H) hd (K.reconstructedOperator C)
  intro η ξ
  exact (Lp.aestronglyMeasurable (K.coeff ξ η)).congr
    ((K.reconstructedOperator_core_ae C ξ η).mono (fun _ h => h.symm))

/-- A bounded measurable representative reconstructed from the scalar kernel. -/
def reconstructedRepresentative : WeakOperatorRepresentative (H := H) μ :=
  WeakOperatorRepresentative.mk (K.reconstructedOperator C) K.bound
    (K.reconstructedOperator_norm_le C)
    (fun ξ => (K.reconstructedOperator_measurable C ξ).1)
    (fun ξ => (K.reconstructedOperator_measurable C ξ).2)

theorem reconstructedRepresentative_norm_le : ‖K.reconstructedRepresentative C‖ ≤ K.bound :=
  WeakOperatorRepresentative.norm_mk_le _ K.bound_nonneg _ _ _

variable [IsFiniteMeasure μ]

/-- Equality on the core extends to equality of all L-infinity coefficients. -/
theorem reconstructedRepresentative_coefficient (ξ η : H) :
    WeakOperatorRepresentative.coefficient (K.reconstructedRepresentative C) ξ η = K.coeff ξ η := by
  symm
  apply K.coeff_eq_of_core
    (WeakOperatorRepresentative.scalarKernel (K.reconstructedRepresentative C)) C
  intro u v
  apply Lp.ext
  filter_upwards [K.reconstructedOperator_core_ae C u v,
    WeakOperatorRepresentative.coefficient_ae (K.reconstructedRepresentative C) u v] with x hK hR
  exact hK.symm.trans hR.symm

end ScalarOperatorKernel

end

end KadisonKastler

end OAI
end


