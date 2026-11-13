-- Prove2me | Definitions.Def_Q260K056
-- name    : Q260K056
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T05:02:15.152797+00:00
-- url     : https://prove2.me/theorems/a2530123-d8c7-489c-a5dd-2094b5e7c92d
-- title:
--   Definitions bundle Q260K056 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 30 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_Dimension`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/Dimension.lean), [`FactorGeneration_DyadicComparison`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/DyadicComparison.lean), [`FactorGeneration_LocalizedStates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/LocalizedStates.lean), [`FactorGeneration_NormalDimension`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/NormalDimension.lean).
--
--   **Imports.** It imports the bundle `Q260K055` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K016`; the statement `OAI_KadisonKastler_projectionCentralSpace_scalar`; the proof of `OAI_KadisonKastler_projectionCentralSpace_scalar`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Definitions.Def_Q260K055

section
-- module Solutions.OAIQ075_KS.FactorGeneration_DyadicComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-! Projection equivalence and subequivalence are witnessed by actual partial
isometries in the original algebra. No dimension or trace oracle is used. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! Finiteness excludes an infinite family of nonzero equivalent orthogonal
projections. The shift and both of its least supports are constructed. -/

/-- The infinite shift omits the first range. Finiteness then forces that
range, and hence the common source projection, to be zero. -/
theorem traceFree_finite_orthogonal_copies_eq_zero
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (r : AlgebraProjection M) (a : ℕ → PartialIsometry M)
    (hs : ∀ i, (a i).support=r)
    (ho : ∀ i j, i≠j → (a i).target.val*(a j).target.val=0) : r.val=0 := by
  let w (i : ℕ) := PartialIsometry.rangeLink (a i) (a (i+1)) ((hs i).trans (hs (i+1)).symm)
  have hw₁ (i : ℕ) : (w i).support=(a i).target := rfl
  have hw₂ (i : ℕ) : (w i).target=(a (i+1)).target := PartialIsometry.rangeLink_target _ _ _
  obtain ⟨v,hv,hvp,hvq⟩ := PartialIsometry.traceFree_orthogonal_sum w
    (by intro i j h; rw [hw₁,hw₁]; exact ho i j h)
    (by intro i j h; rw [hw₂,hw₂]; exact ho (i+1) (j+1) (by omega))
  have hle : v.target ≤ v.support := by
    apply (hvq v.support).mpr
    intro i
    rw [hw₂,← hw₁ (i+1)]
    exact PartialIsometry.support_mono (hv (i+1))
  have he : v.target=v.support := v.target_eq_support_of_finite hfinite hle
  let c : AlgebraProjection M := ⟨1-(a 0).target.val,(a 0).target.property.one_sub⟩
  have hc : v.target ≤ c := by
    apply (hvq c).mpr
    intro i
    rw [hw₂]
    change (1-(a 0).target.val)*(a (i+1)).target.val=(a (i+1)).target.val
    rw [sub_mul,one_mul,ho 0 (i+1) (by omega),sub_zero]
  have h0 : (a 0).target ≤ c := by
    apply (PartialIsometry.support_mono (hv 0)).trans
    rw [← he]
    exact hc
  have hz : (a 0).target.val=0 := by
    change (1-(a 0).target.val)*(a 0).target.val=(a 0).target.val at h0
    rw [sub_mul,one_mul,(a 0).target.property.isIdempotentElem.eq,sub_self] at h0
    exact h0.symm
  have ha : (a 0).val=0 := by
    have h := (a 0).target_mul
    rw [hz,zero_mul] at h
    exact h.symm
  rw [← hs 0,← (a 0).initial,ha,star_zero,zero_mul]

/-- Subequivalence into every member of an orthogonal sequence is impossible
for a nonzero projection in a finite algebra. -/
theorem traceFree_finite_subequivalent_orthogonal_eq_zero
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (r : AlgebraProjection M) (q : ℕ → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0)
    (h : ∀ i, r.Subequivalent (q i)) : r.val=0 := by
  choose a hs ht using h
  exact traceFree_finite_orthogonal_copies_eq_zero hfinite r a hs (by
    intro i j hij
    exact projection_orthogonal_of_le (ho i j hij) (ht i) (ht j))

/-! Finite comparison and cancellation with actual partial isometries.
No trace, dimension, or representation is assumed. -/
end Tracial

/-! Actual finite sums of orthogonal partial isometries and finite subsets of
equivalent partitions. The finite subset is arbitrary, without an index order. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem traceFreeDyadicSibling_le (p : AlgebraProjection M) (n : ℕ) :
    traceFreeDyadicSibling hfactor hdiff p n ≤ traceFreeDyadicReference hfactor hdiff p n :=
  traceFreeDyadic_child_le hfactor hdiff p n (dyadicFalseIndex n) true

theorem traceFreeDyadicReference_sibling_orthogonal (p : AlgebraProjection M) (n : ℕ) :
    (traceFreeDyadicReference hfactor hdiff p (n+1)).val*
      (traceFreeDyadicSibling hfactor hdiff p n).val=0 := by
  apply EquivalentPartition.orthogonal
  exact fun h => Bool.false_ne_true (congrArg Prod.snd h)

theorem traceFreeDyadicSibling_orthogonal (p : AlgebraProjection M) (i j : ℕ) (hij : i≠j) :
    (traceFreeDyadicSibling hfactor hdiff p i).val*
      (traceFreeDyadicSibling hfactor hdiff p j).val=0 := by
  have hlt (i j : ℕ) (h : i<j) :
      (traceFreeDyadicSibling hfactor hdiff p i).val*
        (traceFreeDyadicSibling hfactor hdiff p j).val=0 := by
    apply projection_orthogonal_of_le
      (PartialIsometry.orthogonal_reverse _ _
        (traceFreeDyadicReference_sibling_orthogonal hfactor hdiff p i)) le_rfl
    exact (traceFreeDyadicSibling_le hfactor hdiff p j).trans
      (traceFreeDyadicReference_antitone hfactor hdiff p (by omega))
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · exact PartialIsometry.orthogonal_reverse _ _ (hlt j i h)

theorem traceFreeDyadicReference_equivalent_sibling (p : AlgebraProjection M) (n : ℕ) :
    (traceFreeDyadicReference hfactor hdiff p (n+1)).Equivalent
      (traceFreeDyadicSibling hfactor hdiff p n) := by
  let E := traceFreeDyadicPartition hfactor hdiff p (n+1)
  exact ⟨E.link (dyadicFalseIndex (n+1)) (dyadicFalseIndex n,true),
    E.link_support _ _,E.link_target _ _⟩

/-- A projection that embeds in every dyadic reference corner must be zero.
Finiteness is used through the constructed infinite shift, not through a trace. -/
theorem traceFree_dyadic_archimedean
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p r : AlgebraProjection M)
    (h : ∀ n, r.Subequivalent (traceFreeDyadicReference hfactor hdiff p n)) : r.val=0 := by
  apply traceFree_finite_subequivalent_orthogonal_eq_zero hfinite r
    (traceFreeDyadicSibling hfactor hdiff p)
    (traceFreeDyadicSibling_orthogonal hfactor hdiff p)
  intro n
  exact AlgebraProjection.subequivalent_trans (h (n+1))
    (traceFreeDyadicReference_equivalent_sibling hfactor hdiff p n).subequivalent

/-- Every nonzero projection eventually fails to fit into the dyadic corners. -/
theorem traceFree_exists_dyadic_obstruction
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p r : AlgebraProjection M) (hr : r.val≠0) :
    ∃ n, ¬r.Subequivalent (traceFreeDyadicReference hfactor hdiff p n) := by
  by_contra hn
  exact hr (traceFree_dyadic_archimedean hfactor hdiff hfinite p r
    (by simpa only [not_exists,not_not] using hn))

/-- Every nonzero projection contains an equivalent copy of every sufficiently
small dyadic reference piece. This supplies the positivity input for dimension. -/
theorem traceFree_eventually_dyadic_subequivalent
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p r : AlgebraProjection M) (hr : r.val≠0) :
    ∃ n, ∀ m, n ≤ m → (traceFreeDyadicReference hfactor hdiff p m).Subequivalent r := by
  obtain ⟨n,hn⟩ := traceFree_exists_dyadic_obstruction hfactor hdiff hfinite p r hr
  have he : (traceFreeDyadicReference hfactor hdiff p n).Subequivalent r :=
    (AlgebraProjection.subequivalent_total hfactor r _).resolve_left hn
  refine ⟨n,fun m hm => ?_⟩
  exact AlgebraProjection.subequivalent_trans (AlgebraProjection.subequivalent_of_le
    (traceFreeDyadicReference_antitone hfactor hdiff p hm)) he

end Tracial

end

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

theorem traceFreeDyadicSup_self (p : AlgebraProjection M) :
    traceFreeDyadicSup hfactor hdiff p p=1 := by
  apply le_antisymm (traceFreeDyadicSup_le_one hfactor hdiff p p)
  rw [← dyadicWeight_univ 0]
  apply traceFreeDyadicSup_lower_bound hfactor hdiff p p 0 Finset.univ
  rw [EquivalentPartition.subset_univ]
  exact AlgebraProjection.subequivalent_refl p

/-- Archimedean comparison makes the supremum strictly positive on nonzero projections. -/
theorem traceFreeDyadicSup_pos
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p q : AlgebraProjection M) (hq : q.val≠0) :
    0 < traceFreeDyadicSup hfactor hdiff p q := by
  obtain ⟨n,hn⟩ := traceFree_eventually_dyadic_subequivalent hfactor hdiff hfinite p q hq
  have h := hn n le_rfl
  have he : ((traceFreeDyadicPartition hfactor hdiff p n).subset {dyadicFalseIndex n}).Subequivalent q := by
    rw [EquivalentPartition.subset_singleton]
    exact h
  apply lt_of_lt_of_le ?_ (traceFreeDyadicSup_lower_bound hfactor hdiff p q n _ he)
  simp only [dyadicWeight,Finset.card_singleton,Nat.cast_one]
  exact div_pos zero_lt_one (pow_pos (by norm_num) _)

end

/-! Common refinements compare arbitrary dyadic levels. The supremum takes
the exact dyadic value on every reference subset projection, and finite
rounding bounds every projection with an explicit error at each level. -/

/-! Orthogonal lower approximants fit disjoint collections of the reference
pieces. Equivalent complements and finite cancellation enforce the capacity. -/

/-! Orthogonal additivity of the constructed dyadic dimension. Numerical
rounding errors tend to zero; every lower and upper bound uses actual
partial-isometry witnesses in the original finite diffuse factor. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- Faithfulness and additivity give strict increase along proper inclusion. -/
theorem traceFreeDyadicSup_strictMono
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hrp : r ≤ p) (hqr : q < r) :
    traceFreeDyadicSup hfactor hdiff p q < traceFreeDyadicSup hfactor hdiff p r := by
  have hle : q ≤ r := le_of_lt hqr
  let s := AlgebraProjection.remainder q r hle
  have hs : s.val≠0 := by
    change r.val-q.val≠0
    intro h
    exact (ne_of_lt hqr) (Subtype.ext (sub_eq_zero.mp h).symm)
  have hpos := traceFreeDyadicSup_pos hfactor hdiff hfinite p s hs
  have he := traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite p q s hp
    (hle.trans hrp) ((AlgebraProjection.remainder_le q r hle).trans hrp)
    (AlgebraProjection.remainder_orthogonal q r hle)
  rw [AlgebraProjection.orthogonalSum_remainder] at he
  linarith

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
theorem traceFree_target_eq_of_dimension_le
    (p q : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p)
    (v : PartialIsometry M) (ht : v.target ≤ q)
    (hd : traceFreeDyadicSup hfactor hdiff p q ≤ traceFreeDyadicSup hfactor hdiff p v.support) :
    v.target=q := by
  by_contra he
  have hlt := traceFreeDyadicSup_strictMono hfactor hdiff hfinite p v.target q hp hqp
    (lt_of_le_of_ne ht he)
  have heq := traceFreeDyadicSup_equivalent hfactor hdiff p
    (show v.support.Equivalent v.target from ⟨v,rfl,rfl⟩)
  linarith

include hfinite in
/-- Real-valued comparison is exactly witnessed projection subequivalence. -/
theorem traceFreeDyadicSup_le_iff_subequivalent
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p) :
    traceFreeDyadicSup hfactor hdiff p q ≤ traceFreeDyadicSup hfactor hdiff p r ↔
      q.Subequivalent r := by
  refine ⟨fun hd => ?_,traceFreeDyadicSup_mono hfactor hdiff p⟩
  rcases AlgebraProjection.subequivalent_total hfactor q r with h | h
  · exact h
  · obtain ⟨v,hv,ht⟩ := h
    have he : v.target=q := traceFree_target_eq_of_dimension_le hfactor hdiff hfinite
      p q hp hqp v ht (by rw [hv]; exact hd)
    exact ⟨v.adjoint,he,le_of_eq (v.adjoint_target.trans hv)⟩

end Tracial

end

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

theorem traceFreeDimension_subequivalent {q r : AlgebraProjection M}
    (h : q.Subequivalent r) :
    traceFreeDimension hfactor hdiff q ≤ traceFreeDimension hfactor hdiff r :=
  traceFreeDyadicSup_mono hfactor hdiff _ h

theorem traceFreeDimension_mono : Monotone (traceFreeDimension hfactor hdiff) :=
  fun _ _ h => traceFreeDimension_subequivalent hfactor hdiff
    (AlgebraProjection.subequivalent_of_le h)

include hfinite in
theorem traceFreeDimension_le_iff_subequivalent
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (q r : AlgebraProjection M) :
    traceFreeDimension hfactor hdiff q ≤ traceFreeDimension hfactor hdiff r ↔
      q.Subequivalent r :=
  traceFreeDyadicSup_le_iff_subequivalent hfactor hdiff hfinite _ q r hunit (one_mul _)

include hfinite in
theorem traceFreeDimension_strictMono (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    StrictMono (traceFreeDimension hfactor hdiff) :=
  fun _ _ h => traceFreeDyadicSup_strictMono hfactor hdiff hfinite _ _ _ hunit (one_mul _) h

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_NormalDimension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Increasing projection suprema and compatible sequential comparison.
The witnesses live in the original algebra; no trace or dimension is used. -/
namespace Tracial

/-! Continuity of the constructed dimension on arbitrary increasing projection
nets. Compatible sequential embeddings are proved first; dimension approximation
then constructs a countable subfamily with the same projection supremum. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem traceFreeDimension_range_bddAbove {I : Type*} (q : I → AlgebraProjection M) :
    BddAbove (Set.range (fun i => traceFreeDimension hfactor hdiff (q i))) :=
  ⟨1,by rintro _ ⟨i,rfl⟩; exact traceFreeDimension_le_one hfactor hdiff (q i)⟩

include hfinite in
/-- Continuity on sequences follows from compatible embeddings into each
concrete dyadic upper approximant of the real supremum. -/
theorem traceFreeDimension_isLUB_sequence
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (q : ℕ → AlgebraProjection M) (hq : Monotone q)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range q) p) :
    traceFreeDimension hfactor hdiff p =
      sSup (Set.range (fun n => traceFreeDimension hfactor hdiff (q n))) := by
  let c := sSup (Set.range (fun n => traceFreeDimension hfactor hdiff (q n)))
  have hb := traceFreeDimension_range_bddAbove hfactor hdiff q
  have hne := Set.range_nonempty (fun n => traceFreeDimension hfactor hdiff (q n))
  have hqc (n : ℕ) : traceFreeDimension hfactor hdiff (q n) ≤ c := le_csSup hb ⟨n,rfl⟩
  have hc : 0 ≤ c := (traceFreeDimension_nonneg hfactor hdiff (q 0)).trans (hqc 0)
  have hc1 : c ≤ 1 := csSup_le hne (by
    rintro _ ⟨n,rfl⟩; exact traceFreeDimension_le_one hfactor hdiff (q n))
  apply le_antisymm ?_ (csSup_le hne (by
    rintro _ ⟨n,rfl⟩
    exact traceFreeDimension_mono hfactor hdiff (hp.1 ⟨n,rfl⟩)))
  apply le_of_all_dyadic_errors
  intro n
  obtain ⟨r,hcr,hrc⟩ := traceFreeDimension_exists_upper hfactor hdiff hfinite hunit c hc hc1 n
  have hqr (k : ℕ) : (q k).Subequivalent r :=
    (traceFreeDimension_le_iff_subequivalent hfactor hdiff hfinite hunit _ _).mp
      ((hqc k).trans hcr)
  exact (traceFreeDimension_subequivalent hfactor hdiff
    (AlgebraProjection.isLUB_subequivalent_of_sequence hfactor hfinite q hq p hp r hqr)).trans hrc

include hfinite in
/-- Construct an increasing countable subfamily whose supremum dimension is
the real supremum of the entire directed family. No countability is assumed. -/
theorem traceFreeDimension_exists_exhausting_sequence
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q) :
    ∃ (a : ℕ → I) (s : AlgebraProjection M), Monotone a ∧
      IsLUB (Set.range (fun n => q (a n))) s ∧
      traceFreeDimension hfactor hdiff s =
        sSup (Set.range (fun i => traceFreeDimension hfactor hdiff (q i))) := by
  classical
  let c := sSup (Set.range (fun i => traceFreeDimension hfactor hdiff (q i)))
  have hb := traceFreeDimension_range_bddAbove hfactor hdiff q
  have hqc (i : I) : traceFreeDimension hfactor hdiff (q i) ≤ c := le_csSup hb ⟨i,rfl⟩
  have hex (n : ℕ) : ∃ i, c-1/2^n < traceFreeDimension hfactor hdiff (q i) := by
    have hn : c-1/2^n < c := sub_lt_self c (by positivity)
    obtain ⟨_,⟨i,rfl⟩,hi⟩ := exists_lt_of_lt_csSup
      (Set.range_nonempty (fun i => traceFreeDimension hfactor hdiff (q i))) hn
    exact ⟨i,hi⟩
  choose f hf using hex
  obtain ⟨a,ha,hfa,_⟩ := exists_monotone_dominating_from f (Classical.choice ‹Nonempty I›)
  obtain ⟨s,hs⟩ := AlgebraProjection.exists_isLUB_monotone (fun n => q (a n)) (hq.comp ha)
  refine ⟨a,s,ha,hs,le_antisymm ?_ ?_⟩
  · rw [traceFreeDimension_isLUB_sequence hfactor hdiff hfinite hunit _ (hq.comp ha) s hs]
    exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨n,rfl⟩; exact hqc (a n))
  · apply le_of_all_dyadic_errors
    intro n
    have hfq := traceFreeDimension_mono hfactor hdiff (hq (hfa n))
    have hqs := traceFreeDimension_mono hfactor hdiff (hs.1 ⟨n,rfl⟩)
    have hfn := hf n
    linarith

include hfinite in
/-- The constructed countable supremum bounds the entire net: adjoining any
one index cannot increase its dimension, so strict increase forces equality. -/
theorem traceFreeDimension_exists_isLUB
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q) :
    ∃ p : AlgebraProjection M, IsLUB (Set.range q) p ∧
      traceFreeDimension hfactor hdiff p =
        sSup (Set.range (fun i => traceFreeDimension hfactor hdiff (q i))) := by
  obtain ⟨a,s,ha,hs,hd⟩ := traceFreeDimension_exists_exhausting_sequence
    hfactor hdiff hfinite hunit q hq
  have hupper (i : I) : q i ≤ s := by
    obtain ⟨b,hb,hab,hib⟩ := exists_monotone_dominating_from a i
    obtain ⟨t,ht⟩ := AlgebraProjection.exists_isLUB_monotone (fun n => q (b n)) (hq.comp hb)
    have hst : s ≤ t := hs.2 (by
      rintro _ ⟨n,rfl⟩; exact (hq (hab n)).trans (ht.1 ⟨n,rfl⟩))
    have htd : traceFreeDimension hfactor hdiff t ≤ traceFreeDimension hfactor hdiff s := by
      rw [hd,traceFreeDimension_isLUB_sequence hfactor hdiff hfinite hunit _ (hq.comp hb) t ht]
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨n,rfl⟩
      exact le_csSup (traceFreeDimension_range_bddAbove hfactor hdiff q) ⟨b n,rfl⟩
    have he : s=t := by
      by_contra hne
      exact (not_lt_of_ge htd) (traceFreeDimension_strictMono hfactor hdiff hfinite hunit
        (lt_of_le_of_ne hst hne))
    rw [he]
    exact (hq (hib 0)).trans (ht.1 ⟨0,rfl⟩)
  refine ⟨s,⟨?_,?_⟩,hd⟩
  · rintro _ ⟨i,rfl⟩; exact hupper i
  · intro p hp
    exact hs.2 (by rintro _ ⟨n,rfl⟩; exact hp ⟨a n,rfl⟩)

include hfinite in
/-- Order continuity on arbitrary nonempty directed projection nets. -/
theorem traceFreeDimension_isLUB_monotone
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range q) p) :
    traceFreeDimension hfactor hdiff p =
      sSup (Set.range (fun i => traceFreeDimension hfactor hdiff (q i))) := by
  obtain ⟨s,hs,hd⟩ := traceFreeDimension_exists_isLUB hfactor hdiff hfinite hunit q hq
  have he : p=s := le_antisymm (hp.2 hs.1) (hs.2 hp.1)
  rw [he]
  exact hd

end Tracial

/-! Original-factor wrapper for normalized faithful order-continuous projection
dimension. This does not assert the existence of a linear trace functional. -/

/-! Exact prescribed dimensions are attained by actual subprojections.
Chain bounds use the proved arbitrary-net continuity of dimension. -/

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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
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
section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_tendsto_monotone
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range q) p) :
    Tendsto (fun i => traceFreeDimension hfactor hdiff (q i)) atTop
      (𝓝 (traceFreeDimension hfactor hdiff p)) := by
  rw [traceFreeDimension_isLUB_monotone hfactor hdiff hfinite hunit q hq p hp]
  exact tendsto_atTop_isLUB ((traceFreeDimension_mono hfactor hdiff).comp hq)
    (isLUB_csSup (Set.range_nonempty _) (traceFreeDimension_range_bddAbove hfactor hdiff q))

include hfinite in
/-- Concrete localization for a real linear combination of the actual vector
functional and the already constructed dimension; no linear trace is assumed. -/
theorem exists_signed_vector_dimension_corner
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (c d : ℝ) (G : AlgebraProjection M) (hG : G.val≠0)
    (hμG : 0 ≤ c*G.vectorValue ξ+d*traceFreeDimension hfactor hdiff G) :
    ∃ F : AlgebraProjection M, F ≤ G ∧ F.val≠0 ∧
      ∀ p, p ≤ F → 0 ≤ c*p.vectorValue ξ+d*traceFreeDimension hfactor hdiff p := by
  apply AlgebraProjection.exists_nonnegative_corner
    (fun p => c*p.vectorValue ξ+d*traceFreeDimension hfactor hdiff p) ?_ ?_ G hG hμG
  · intro p q ho
    have hν : (orthogonalSum p q ho).vectorValue ξ=p.vectorValue ξ+q.vectorValue ξ := by
      change (inner ℂ ξ (p.val.val ξ+q.val.val ξ)).re=_
      rw [inner_add_right,Complex.add_re]
      rfl
    have hD := traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ p q hunit (one_mul _) (one_mul _) ho
    change traceFreeDimension hfactor hdiff (orthogonalSum p q ho)=
      traceFreeDimension hfactor hdiff p+traceFreeDimension hfactor hdiff q at hD
    rw [hν,hD]
    ring
  · intro I _ _ _ a ha p hp
    exact ((AlgebraProjection.vectorValue_tendsto_monotone a ha p hp ξ).const_mul c).add
      ((traceFreeDimension_tendsto_monotone hfactor hdiff hfinite hunit a ha p hp).const_mul d)

include hfinite in
theorem exists_vector_dimension_lower_corner
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (G : AlgebraProjection M) (hG : G.val≠0) :
    ∃ F : AlgebraProjection M, F ≤ G ∧ F.val≠0 ∧ ∀ p, p ≤ F →
      G.vectorValue ξ*traceFreeDimension hfactor hdiff p ≤
        p.vectorValue ξ*traceFreeDimension hfactor hdiff G := by
  obtain ⟨F,hFG,hF,h⟩ := exists_signed_vector_dimension_corner hfactor hdiff hfinite hunit
    ξ (traceFreeDimension hfactor hdiff G) (-G.vectorValue ξ) G hG (by nlinarith)
  exact ⟨F,hFG,hF,fun p hp => by have hh := h p hp; nlinarith⟩

include hfinite in
theorem exists_vector_dimension_upper_corner
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (G : AlgebraProjection M) (hG : G.val≠0) :
    ∃ F : AlgebraProjection M, F ≤ G ∧ F.val≠0 ∧ ∀ p, p ≤ F →
      p.vectorValue ξ*traceFreeDimension hfactor hdiff G ≤
        G.vectorValue ξ*traceFreeDimension hfactor hdiff p := by
  obtain ⟨F,hFG,hF,h⟩ := exists_signed_vector_dimension_corner hfactor hdiff hfinite hunit
    ξ (-traceFreeDimension hfactor hdiff G) (G.vectorValue ξ) G hG (by nlinarith)
  exact ⟨F,hFG,hF,fun p hp => by have hh := h p hp; nlinarith⟩

end

/-! Tight multiplicative localization of an actual Hilbert vector functional
against the constructed projection dimension. The corner is constructed. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- An actual unit vector admits a nonzero corner on which every projection
value is between a D(p) and (1+ε)a D(p), with a strictly positive. -/
theorem exists_vector_dimension_localization
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (hξ : ‖ξ‖=1) (ε : ℝ) (hε : 0<ε) :
    ∃ (E : AlgebraProjection M) (a : ℝ), E.val≠0 ∧ 0<a ∧
      ∀ p : AlgebraProjection M, p ≤ E →
        a*traceFreeDimension hfactor hdiff p ≤ (inner ℂ ξ (p.val.val ξ)).re ∧
        (inner ℂ ξ (p.val.val ξ)).re ≤ (1+ε)*a*traceFreeDimension hfactor hdiff p := by
  classical
  let ν := AlgebraProjection.vectorValue (M := M) ξ
  let D := traceFreeDimension hfactor hdiff
  let oneP : AlgebraProjection M := ⟨1,IsStarProjection.one _⟩
  have hν1 : ν oneP=1 := by
    change (inner ℂ ξ ξ).re=1
    rw [inner_self_eq_norm_sq_to_K,hξ]
    norm_num
  have hD1 : D oneP=1 := traceFreeDyadicSup_self hfactor hdiff oneP
  have hDpos (p : AlgebraProjection M) (hp : p.val≠0) : 0<D p :=
    traceFreeDyadicSup_pos hfactor hdiff hfinite oneP p hp
  obtain ⟨F,_,hF,hlo⟩ := exists_vector_dimension_lower_corner
    hfactor hdiff hfinite hunit ξ oneP hunit
  have hFbound (p : AlgebraProjection M) (hp : p ≤ F) : D p ≤ ν p := by
    have hh := hlo p hp
    change ν oneP*D p ≤ ν p*D oneP at hh
    simpa only [hν1,hD1,one_mul,mul_one] using hh
  let R : Set ℝ := {b | ∃ p : AlgebraProjection M, p ≤ F ∧ p.val≠0 ∧ b=ν p/D p}
  have hRne : R.Nonempty := ⟨ν F/D F,F,le_rfl,hF,rfl⟩
  have hRlower : ∀ b ∈ R, 1 ≤ b := by
    rintro b ⟨p,hp,hpn,rfl⟩
    exact (le_div_iff₀ (hDpos p hpn)).mpr (by simpa only [one_mul] using hFbound p hp)
  have hRb : BddBelow R := ⟨1,hRlower⟩
  let a := sInf R
  have ha1 : 1 ≤ a := le_csInf hRne hRlower
  have ha : 0<a := lt_of_lt_of_le (by norm_num) ha1
  have hnear : a < (1+ε)*a := by nlinarith
  obtain ⟨_,⟨r,hrF,hr,hratio⟩,hnearR⟩ := exists_lt_of_csInf_lt hRne hnear
  rw [hratio] at hnearR
  obtain ⟨E,hEr,hE,hhi⟩ := exists_vector_dimension_upper_corner
    hfactor hdiff hfinite hunit ξ r hr
  refine ⟨E,a,hE,ha,?_⟩
  intro p hp
  by_cases hp0 : p.val=0
  · have hν0 : ν p=0 := by
      change (inner ℂ ξ (p.val.val ξ)).re=0
      rw [hp0]
      simp
    have hD0 : D p=0 := traceFreeDyadicSup_zero hfactor hdiff oneP p hunit hp0
    change a*D p ≤ ν p ∧ ν p ≤ (1+ε)*a*D p
    rw [hν0,hD0]
    simp
  · have hDp : 0<D p := hDpos p hp0
    have hpF : p ≤ F := hp.trans (hEr.trans hrF)
    have hap : a ≤ ν p/D p := csInf_le hRb ⟨p,hpF,hp0,rfl⟩
    have hloP : a*D p ≤ ν p := (le_div_iff₀ hDp).mp hap
    have hDr : 0<D r := hDpos r hr
    have hhiP := hhi p hp
    change ν p*D r ≤ ν r*D p at hhiP
    have hratioP : ν p ≤ (ν r/D r)*D p := by
      apply (mul_le_mul_iff_right₀ hDr).mp
      calc D r*ν p = ν p*D r := mul_comm _ _
           _ ≤ ν r*D p := hhiP
           _ = D r*(ν r/D r*D p) := by field_simp
    have hbound : (ν r/D r)*D p ≤ (1+ε)*a*D p :=
      mul_le_mul_of_nonneg_right hnearR.le hDp.le
    exact ⟨hloP,hratioP.trans hbound⟩

end

/-! Positive spectral approximants inside an actual projection corner, and
extension of localized projection inequalities to positive operators. -/
open scoped BigOperators CStarAlgebra

/-! Projection localization yields actual positive-operator inequalities for
bounded linear functionals, and a nearly cyclic functional on the corner. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.localizedStarOrder
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.localizedCStar
attribute [local instance] OAI.Generator.Tracial.localizedOrder
local instance localizedPreorder_r3610e8_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.localizedLE
theorem positive_functional_bounds_of_projection_bounds
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) (E : AlgebraProjection M)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hproj : ∀ p : AlgebraProjection M, p ≤ E →
      a*traceFreeDimension hfactor hdiff p ≤ (φ p.val).re ∧
      (φ p.val).re ≤ b*traceFreeDimension hfactor hdiff p)
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (hEx : E.val*x=x) :
    a*(dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re ≤ (φ x).re ∧
      (φ x).re ≤ b*(dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  let t := dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint
  have hxE : x*E.val=x := by
    simpa only [star_mul,E.property.isSelfAdjoint.star_eq,hx.isSelfAdjoint.star_eq]
      using congrArg star hEx
  have happrox (ε : ℝ) (hε : 0<ε) :
      a*t.re ≤ (φ x).re+ε ∧ (φ x).re ≤ b*t.re+ε := by
    let C := a+b+‖φ‖+1
    have hC : 0<C := by dsimp [C] <;> positivity
    let δ := ε/C
    have hδ : 0<δ := div_pos hε hC
    have hCδ : C*δ=ε := mul_div_cancel₀ _ hC.ne'
    obtain ⟨Q,c,hc,hQ,herr⟩ := exists_positive_corner_spectral_approximation E x hx hEx δ hδ
    let y : M.toStarSubalgebra := ∑ i, (c i : ℂ) • (Q.piece i).val
    let w : ℝ := ∑ i, c i*traceFreeDimension hfactor hdiff (Q.piece i)
    let v : ℝ := (φ y).re
    have hw : (w : ℂ)=∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
      simp only [w,Complex.ofReal_sum,Complex.ofReal_mul]
    have hv : v=∑ i, c i*(φ (Q.piece i).val).re := by
      simp only [v,y,map_sum,map_smul,smul_eq_mul,Complex.re_sum,Complex.mul_re,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    have hav : a*w ≤ v := by
      rw [hv,show a*w=∑ i, c i*(a*traceFreeDimension hfactor hdiff (Q.piece i)) by
        simp only [w,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (hproj (Q.piece i) (Q.piece_le i)).1 (hc i))
    have hvb : v ≤ b*w := by
      rw [hv,show b*w=∑ i, c i*(b*traceFreeDimension hfactor hdiff (Q.piece i)) by
        simp only [w,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (hproj (Q.piece i) (Q.piece_le i)).2 (hc i))
    have hspec := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx.isSelfAdjoint).2.corner_bound
      hfactor hdiff E (hEx.trans hxE.symm) Q (fun i => (c i : ℂ)) hQ
    have htw : |t.re-w| ≤ δ := by
      have h := Complex.abs_re_le_norm (t-(w : ℂ))
      rw [Complex.sub_re,Complex.ofReal_re] at h
      apply h.trans
      rw [hw]
      exact hspec.trans herr.le
    have hφ : |(φ x).re-v| ≤ ‖φ‖*δ := by
      have he : (φ x).re-v=(φ (x-y)).re := by rw [map_sub,Complex.sub_re]
      rw [he]
      exact (Complex.abs_re_le_norm _).trans ((φ.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left herr.le (norm_nonneg φ)))
    have htw' := abs_le.mp htw
    have hφ' := abs_le.mp hφ
    have had := mul_nonneg ha hδ.le
    have hbd := mul_nonneg hb hδ.le
    dsimp only [C] at hCδ
    constructor <;> nlinarith
  constructor
  · apply le_of_forall_pos_le_add
    intro ε hε
    exact (happrox ε hε).1
  · apply le_of_forall_pos_le_add
    intro ε hε
    exact (happrox ε hε).2

/-- Concrete projection and positive-operator localization, with an actual
bounded complex-linear functional and a nonzero constructed corner. -/
theorem exists_localized_vector_functional
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (hξ : ‖ξ‖=1) (ε : ℝ) (hε : 0<ε) :
    ∃ (E : AlgebraProjection M) (a : ℝ), E.val≠0 ∧ 0<a ∧
      ∀ (x : M.toStarSubalgebra) (hx : 0 ≤ x), E.val*x=x →
        a*(dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re ≤
          (vectorFunctional ξ x).re ∧
        (vectorFunctional ξ x).re ≤
          (1+ε)*a*(dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  obtain ⟨E,a,hE,ha,hp⟩ := exists_vector_dimension_localization hfactor hdiff hfinite hunit ξ hξ ε hε
  refine ⟨E,a,hE,ha,?_⟩
  intro x hx hEx
  exact positive_functional_bounds_of_projection_bounds hfactor hdiff hfinite hunit
    (vectorFunctional ξ) E a ((1+ε)*a) ha.le (mul_nonneg (by linarith) ha.le) hp x hx hEx

end

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


