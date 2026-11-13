-- Prove2me | Definitions.Def_Q260K053
-- name    : Q260K053
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:39:49.78145+00:00
-- url     : https://prove2.me/theorems/24fc2457-fba5-4061-bd3a-8d2f15fd56f3
-- title:
--   Definitions bundle Q260K053 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 49 declarations of OpenAI's Lean: 6 definitions and 43 theorems. The definitions and types are `OAI.Generator.Tracial.EquivalentPartition.link`, `OAI.Generator.Tracial.traceFreeBinaryPartition`, `OAI.Generator.Tracial.traceFreeDimension`, `OAI.Generator.Tracial.traceFreeDyadicCut`, `OAI.Generator.Tracial.traceFreeDyadicPartition`, `OAI.Generator.Tracial.traceFreeDyadicSup`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_Dimension`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/Dimension.lean), [`FactorGeneration_DyadicComparison`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/DyadicComparison.lean), [`FactorGeneration_FiniteComparison`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/FiniteComparison.lean).
--
--   **Imports.** It imports the bundles `Q260K000` and `Q260K001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K054`; the statement `OAI_KadisonKastler_exists_finite_uniform_pinching_gap`; the proofs of `OAI_KadisonKastler_constructed_exists_common_action_of_comparison_normalizers` and `OAI_KadisonKastler_exists_finite_uniform_pinching_gap`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
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
import Definitions.Def_Q260K000
import Definitions.Def_Q260K001

section
-- module Solutions.OAIQ075_KS.FactorGeneration_FiniteComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.PopaCorner.instRing
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
namespace Tracial
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace PartialIsometry

theorem traceFree_orthogonal_chain_upper_bound (c : Set (PartialIsometry M))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (p : AlgebraProjection M) (hp : ∀ v ∈ c, v.support ≤ p)
    (hq : ∀ v ∈ c, v.target ≤ p)
    (ho : ∀ v ∈ c, v.support.val*v.target.val=0) :
    ∃ v : PartialIsometry M, (∀ w ∈ c, w ≤ v) ∧ v.support ≤ p ∧ v.target ≤ p ∧
      v.support.val*v.target.val=0 := by
  let : Nonempty c := hne.to_subtype
  let : IsDirected c (· ≤ ·) := ⟨by
    intro u v
    rcases hc.total u.property v.property with h | h
    · exact ⟨v,h,le_rfl⟩
    · exact ⟨u,le_rfl,h⟩⟩
  obtain ⟨v,hv,hvp,hvq,hvo⟩ := traceFree_orthogonal_monotone_upper_bound
    (fun w : c => w.val) (fun _ _ h => h) p
    (fun w => hp w.val w.property) (fun w => hq w.val w.property)
    (fun w => ho w.val w.property)
  exact ⟨v,fun w hw => hv ⟨w,hw⟩,hvp,hvq,hvo⟩

theorem traceFree_exists_maximal_orthogonal (p : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ p ∧
      v.support.val*v.target.val=0 ∧
      ∀ w : PartialIsometry M, w.support ≤ p → w.target ≤ p →
        w.support.val*w.target.val=0 → v ≤ w → w ≤ v := by
  let S : Set (PartialIsometry M) :=
    {v | v.support ≤ p ∧ v.target ≤ p ∧ v.support.val*v.target.val=0}
  obtain ⟨v,hv⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · obtain ⟨v,hcv,hvp,hvq,hvo⟩ := traceFree_orthogonal_chain_upper_bound c hchain hne p
        (fun w hw => (hc hw).1) (fun w hw => (hc hw).2.1) (fun w hw => (hc hw).2.2)
      exact ⟨v,⟨hvp,hvq,hvo⟩,hcv⟩
    · refine ⟨zero,⟨?_,?_,?_⟩,?_⟩
      · change p.val*0=0
        exact mul_zero _
      · apply (zero.target_le_iff_mul p).mpr
        exact mul_zero _
      · exact zero_mul _
      · intro w hw
        exact (hne ⟨w,hw⟩).elim)
  exact ⟨v,hv.1.1,hv.1.2.1,hv.1.2.2,fun w hp hq ho h => hv.2 ⟨hp,hq,ho⟩ h⟩

/-! Simultaneous least initial and final support bounds for arbitrary directed
partial-isometry nets. The actual ultralimit is chosen once for all bounds. -/

end PartialIsometry
end Tracial

/-! Complete actual partial isometries to unitaries in a finite factor.
The construction uses projection comparison and finiteness, without a trace. -/
open scoped CStarAlgebra

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_DyadicComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
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
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}

/-- The two equivalent halves are constructed by an actual partial isometry.
No trace, finite-isometry property, or separability is needed for this lemma. -/
theorem traceFree_exists_halving
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support.val*v.target.val=0 ∧
      v.support.val+v.target.val=p.val := by
  obtain ⟨v,hvp,hvq,hvo,hmax⟩ := PartialIsometry.traceFree_exists_maximal_orthogonal p
  let t := orthogonalSum v.support v.target hvo
  have htp : t ≤ p := orthogonalSum_le hvo hvp hvq
  let r : AlgebraProjection M := ⟨p.val-t.val,t.property.sub_of_mul_eq_right p.property htp⟩
  have hrp : r ≤ p := by
    change p.val*(p.val-t.val)=p.val-t.val
    rw [mul_sub,p.property.isIdempotentElem.eq,htp]
  have htr : t.val*r.val=0 := by
    change t.val*(p.val-t.val)=0
    rw [mul_sub,projection_mul_of_le htp,t.property.isIdempotentElem.eq,sub_self]
  have hr0 : r.val=0 := by
    by_contra hr
    obtain ⟨q,s,hqr,hsr,hq0,hs0,hqs,_⟩ := traceFree_exists_orthogonal_split hdiff r hr
    obtain ⟨w,hwq,hws,hw0⟩ :=
      traceFree_exists_nonzero_partialIsometry_between_projections hfactor q s hq0 hs0
    have hwr : w.support ≤ r := hwq.trans hqr
    have hwtr : w.target ≤ r := hws.trans hsr
    have hvt : v.support ≤ t := le_orthogonalSum_left _ _ hvo
    have hvtt : v.target ≤ t := le_orthogonalSum_right _ _ hvo
    have hpw := projection_orthogonal_of_le htr hvt hwr
    have hqw := projection_orthogonal_of_le htr hvtt hwtr
    have hcross := projection_orthogonal_of_le htr hvt hwtr
    have hcross' := PartialIsometry.orthogonal_reverse _ _
      (projection_orthogonal_of_le htr hvtt hwr)
    have hwo := projection_orthogonal_of_le hqs hwq hws
    let u := v.patch w hpw hqw
    have hup : u.support ≤ p := orthogonalSum_le hpw hvp (hwr.trans hrp)
    have huq : u.target ≤ p := by
      change p.val*u.target.val=u.target.val
      rw [PartialIsometry.patch_target]
      rw [mul_add,hvq,show p.val*w.target.val=w.target.val from hwtr.trans hrp]
    have huo : u.support.val*u.target.val=0 := by
      rw [PartialIsometry.patch_target]
      change (v.support.val+w.support.val)*(v.target.val+w.target.val)=0
      rw [add_mul,mul_add,mul_add,hvo,hcross,hcross',hwo,add_zero,zero_add]
    have hvu : v ≤ u := v.le_patch w hpw hqw
    exact (v.patch_ne w hpw hqw hw0) (le_antisymm (hmax u hup huq huo hvu) hvu)
  exact ⟨v,hvo,(sub_eq_zero.mp hr0).symm⟩

end Tracial

end

/-! Finite partitions with explicit equivalence witnesses and compatible binary
refinement. The common initial projection is halved once and its two pieces
are transported to every old piece, so all new pieces remain equivalent. -/
section
open scoped BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Every ordered pair of pieces has a displayed equivalence witness. -/
def link (E : EquivalentPartition p ι) (i j : ι) : PartialIsometry M :=
  (E.leg j).compose (E.leg i).adjoint (by
    have h : (E.leg i).adjoint.target=(E.leg i).support := by
      apply Subtype.ext
      change star (E.leg i).val*star (star (E.leg i).val)=(E.leg i).support.val
      rw [star_star,(E.leg i).initial]
    rw [h,E.initial,E.initial])

theorem link_support (E : EquivalentPartition p ι) (i j : ι) :
    (E.link i j).support=(E.leg i).target := rfl

theorem link_target (E : EquivalentPartition p ι) (i j : ι) :
    (E.link i j).target=(E.leg j).target := by
  apply Subtype.ext
  change ((E.leg j).val*star (E.leg i).val)*star ((E.leg j).val*star (E.leg i).val)=_
  calc _ = (E.leg j).val*(star (E.leg i).val*(E.leg i).val)*star (E.leg j).val := by
           simp only [star_mul,star_star,mul_assoc]
       _ = (E.leg j).val*star (E.leg j).val := by
           rw [(E.leg i).initial,E.initial,← E.initial j,(E.leg j).mul_support]
       _ = _ := rfl

theorem refine_parent (E : EquivalentPartition p ι) (F : EquivalentPartition E.base κ) (i : ι) :
    (∑ j, ((E.refine F).leg (i,j)).target.val)=(E.leg i).target.val := by
  change (∑ j, ((E.leg i).compose (F.leg j) (by rw [E.initial]; exact F.bound j)).target.val)=_
  simp only [PartialIsometry.compose_target,← Finset.sum_mul,← Finset.mul_sum,F.total]
  rw [← E.initial i,(E.leg i).mul_support]
  rfl

end EquivalentPartition
end Tracial

/-! Coherent dyadic equivalent partitions and matrix units, constructed from
scalar center and diffuseness without a trace. DyadicIndex is reused as a
finite binary index type; no tracial partition construction is used. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A partition of a nonzero projection has no zero piece, since every
piece is equivalent to every other piece by the displayed links. -/
theorem target_ne_zero (E : EquivalentPartition p ι) (hp : p.val≠0) (i : ι) :
    (E.leg i).target.val≠0 := by
  intro hi
  have hz (j : ι) : (E.leg j).target.val=0 := by
    have hw : (E.link i j).val=0 := by
      have hm := (E.link i j).mul_support
      rw [E.link_support,hi,mul_zero] at hm
      exact hm.symm
    rw [← E.link_target i j]
    change (E.link i j).val*star (E.link i j).val=0
    rw [hw,zero_mul]
  have ht := E.total
  simp only [hz,Finset.sum_const_zero] at ht
  exact hp ht.symm

end EquivalentPartition

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

/-- Choose the actual two-leg partition supplied by trace-free halving. -/
def traceFreeBinaryPartition (p : AlgebraProjection M) : EquivalentPartition p Bool :=
  let h := traceFree_exists_halving hfactor hdiff p
  EquivalentPartition.ofHalving h.choose h.choose_spec.1 h.choose_spec.2

/-- A coherent family: each successor halves the previous common initial
projection once and transports that halving to all its equivalent pieces. -/
def traceFreeDyadicPartition (p : AlgebraProjection M) :
    (n : ℕ) → EquivalentPartition p (DyadicIndex n)
  | 0 => EquivalentPartition.singleton p
  | n+1 =>
    let E := traceFreeDyadicPartition p n
    E.refine (traceFreeBinaryPartition hfactor hdiff E.base)

end Tracial

end

/-! Actual sums of countable orthogonal partial isometries, including least
initial/final support identities. No trace or countable-cofinality premise. -/

/-! Actual finite sums of orthogonal partial isometries and finite subsets of
equivalent partitions. The finite subset is arbitrary, without an index order. -/
open scoped BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem subset_le_iff (E : EquivalentPartition p ι) (s : Finset ι) (q : AlgebraProjection M) :
    E.subset s ≤ q ↔ ∀ i ∈ s, (E.leg i).target ≤ q :=
  AlgebraProjection.finsetSum_le_iff _ _ _ _

theorem subset_le (E : EquivalentPartition p ι) (s : Finset ι) : E.subset s ≤ p :=
  (E.subset_le_iff s p).mpr (fun i _ => E.bound i)

theorem subset_mono (E : EquivalentPartition p ι) {s t : Finset ι} (h : s ⊆ t) :
    E.subset s ≤ E.subset t :=
  (E.subset_le_iff s _).mpr (fun i hi => (E.subset_le_iff t _).mp le_rfl i (h hi))

theorem subset_univ (E : EquivalentPartition p ι) : E.subset Finset.univ=p :=
  Subtype.ext E.total

theorem subset_empty (E : EquivalentPartition p ι) : (E.subset ∅).val=0 := by
  simp only [subset_val,Finset.sum_empty]

/-- A bijection of subsets gives a sum of explicit matrix-unit links. -/
theorem subset_equivalent_of_equiv (E : EquivalentPartition p ι) (s t : Finset ι)
    (e : s ≃ t) : (E.subset s).Equivalent (E.subset t) := by
  let a (i : s) := E.link i.val (e i).val
  obtain ⟨v,_,hs,ht⟩ := PartialIsometry.exists_finsetSum a Finset.univ
    (by
      intro i _ j _ hij
      exact E.orthogonal i.val j.val (fun h => hij (Subtype.ext h)))
    (by
      intro i _ j _ hij
      change (E.link i.val (e i).val).target.val*(E.link j.val (e j).val).target.val=0
      rw [E.link_target,E.link_target]
      exact E.orthogonal _ _ (fun h => hij (e.injective (Subtype.ext h))))
  refine ⟨v,Subtype.ext ?_,Subtype.ext ?_⟩
  · rw [hs]
    change (∑ i : s, (E.leg i.val).target.val)=∑ i ∈ s, (E.leg i).target.val
    simpa only [Finset.attach_eq_univ] using
      (Finset.sum_attach s (fun i => (E.leg i).target.val))
  · rw [ht]
    change (∑ i : s, (E.link i.val (e i).val).target.val)=_
    simp only [E.link_target]
    rw [e.sum_comp (fun i : t => (E.leg i.val).target.val)]
    change (∑ i : t, (E.leg i.val).target.val)=∑ i ∈ t, (E.leg i).target.val
    simpa only [Finset.attach_eq_univ] using
      (Finset.sum_attach t (fun i => (E.leg i).target.val))

theorem subset_equivalent_of_card_eq (E : EquivalentPartition p ι) (s t : Finset ι)
    (h : s.card=t.card) : (E.subset s).Equivalent (E.subset t) :=
  E.subset_equivalent_of_equiv s t (Finset.equivOfCardEq h)

/-- Subset sums stay compatible with refinement to all children. -/
theorem subset_refine {κ : Type*} [Fintype κ] (E : EquivalentPartition p ι)
    (F : EquivalentPartition E.base κ) (s : Finset ι) :
    (E.refine F).subset (s ×ˢ Finset.univ)=E.subset s := by
  apply Subtype.ext
  rw [subset_val,Finset.sum_product]
  exact Finset.sum_congr rfl (fun i _ => E.refine_parent F i)

/-! Exact finite cardinal comparison of sums of equivalent nonzero projections.
Finiteness prevents a larger collection from embedding in a smaller one. -/

theorem subset_mul_piece_of_not_mem (E : EquivalentPartition p ι) (s : Finset ι)
    (i : ι) (hi : i ∉ s) : (E.subset s).val*(E.leg i).target.val=0 := by
  rw [subset_val,Finset.sum_mul]
  exact Finset.sum_eq_zero (fun j hj => E.orthogonal j i (fun h => hi (h ▸ hj)))

theorem subset_le_subset_iff (E : EquivalentPartition p ι) (hp : p.val≠0)
    (s t : Finset ι) : E.subset s ≤ E.subset t ↔ s ⊆ t := by
  constructor
  · intro h i hi
    by_contra hit
    have hh := (E.subset_le_iff s _).mp h i hi
    change (E.subset t).val*(E.leg i).target.val=(E.leg i).target.val at hh
    rw [E.subset_mul_piece_of_not_mem t i hit] at hh
    exact E.target_ne_zero hp i hh.symm
  · exact E.subset_mono

theorem subset_subequivalent_of_card_le (E : EquivalentPartition p ι)
    (s t : Finset ι) (h : s.card ≤ t.card) : (E.subset s).Subequivalent (E.subset t) := by
  obtain ⟨u,hut,hu⟩ := Finset.exists_subset_card_eq h
  exact AlgebraProjection.subequivalent_trans
    (E.subset_equivalent_of_card_eq s u hu.symm).subequivalent
    (AlgebraProjection.subequivalent_of_le (E.subset_mono hut))

/-- The witness-based comparison agrees exactly with cardinal comparison. -/
theorem subset_subequivalent_iff_card_le
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (E : EquivalentPartition p ι) (hp : p.val≠0) (s t : Finset ι) :
    (E.subset s).Subequivalent (E.subset t) ↔ s.card ≤ t.card := by
  refine ⟨fun h => ?_,E.subset_subequivalent_of_card_le s t⟩
  by_contra hn
  have hlt : t.card < s.card := Nat.lt_of_not_ge hn
  obtain ⟨u,hus,hu⟩ := Finset.exists_subset_card_eq (Nat.le_of_lt hlt)
  have hsu : (E.subset s).Subequivalent (E.subset u) :=
    AlgebraProjection.subequivalent_trans h
      (E.subset_equivalent_of_card_eq t u hu.symm).subequivalent
  have hle : E.subset u ≤ E.subset s := E.subset_mono hus
  have he : E.subset u=E.subset s := AlgebraProjection.eq_of_equivalent_of_le hfinite
    (AlgebraProjection.equivalent_of_mutual_subequivalent hfinite
      (AlgebraProjection.subequivalent_of_le hle) hsu) hle
  have hs : s ⊆ u := (E.subset_le_subset_iff hp s u).mp (le_of_eq he.symm)
  have hc := Finset.card_le_card hs
  omega

theorem subset_orthogonal_of_disjoint (E : EquivalentPartition p ι)
    (s t : Finset ι) (h : Disjoint s t) : (E.subset s).val*(E.subset t).val=0 := by
  rw [subset_val,subset_val,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero (fun j hj => E.orthogonal i j (fun he =>
    Finset.disjoint_left.mp h hi (he.symm ▸ hj)))

theorem subset_union [DecidableEq ι] (E : EquivalentPartition p ι)
    (s t : Finset ι) (h : Disjoint s t) :
    E.subset (s ∪ t)=orthogonalSum (E.subset s) (E.subset t)
      (E.subset_orthogonal_of_disjoint s t h) :=
  Subtype.ext (Finset.sum_union h)

theorem subset_insert [DecidableEq ι] (E : EquivalentPartition p ι)
    (s : Finset ι) (i : ι) (hi : i ∉ s) :
    (E.subset (insert i s)).val=(E.subset s).val+(E.leg i).target.val := by
  rw [subset_val,Finset.sum_insert hi,add_comm]
  rfl

end EquivalentPartition
end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
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
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem exists_maximal_fitting_subset (E : EquivalentPartition p ι) (q : AlgebraProjection M) :
    ∃ s : Finset ι, (E.subset s).Subequivalent q ∧
      ∀ t : Finset ι, (E.subset t).Subequivalent q → t.card ≤ s.card := by
  classical
  let F : Finset (Finset ι) := Finset.univ.filter (fun s => (E.subset s).Subequivalent q)
  have h0 : (E.subset ∅).Subequivalent q := AlgebraProjection.subequivalent_of_le (by
    change q.val*(E.subset ∅).val=(E.subset ∅).val
    rw [E.subset_empty,mul_zero])
  have hF : F.Nonempty := ⟨∅,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h0⟩⟩
  obtain ⟨s,hs,hmax⟩ := F.exists_max_image Finset.card hF
  exact ⟨s,(Finset.mem_filter.mp hs).2,fun t ht =>
    hmax t (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩)⟩

/-- A further piece in the remainder would enlarge the fitting subset. -/
theorem maximal_remainder_not_subequivalent (E : EquivalentPartition p ι)
    (q : AlgebraProjection M) (s : Finset ι)
    (hmax : ∀ t : Finset ι, (E.subset t).Subequivalent q → t.card ≤ s.card)
    (v : PartialIsometry M) (hv : v.support=E.subset s) (ht : v.target ≤ q)
    (i : ι) (hi : i ∉ s) :
    ¬(E.leg i).target.Subequivalent (AlgebraProjection.remainder v.target q ht) := by
  classical
  intro h
  obtain ⟨w,hw,hwr⟩ := h
  have ho₁ : v.support.val*w.support.val=0 := by
    rw [hv,hw]
    exact E.subset_mul_piece_of_not_mem s i hi
  have ho₂ : v.target.val*w.target.val=0 :=
    projection_orthogonal_of_le (AlgebraProjection.remainder_orthogonal v.target q ht)
      le_rfl hwr
  let u := v.patch w ho₁ ho₂
  have hus : u.support=E.subset (insert i s) := Subtype.ext (by
    change v.support.val+w.support.val=_
    rw [hv,hw,E.subset_insert s i hi])
  have hut : u.target ≤ q := by
    have he : u.target=orthogonalSum v.target w.target ho₂ :=
      Subtype.ext (v.patch_target w ho₁ ho₂)
    rw [he]
    exact orthogonalSum_le ho₂ ht (hwr.trans (AlgebraProjection.remainder_le _ _ ht))
  have hc := hmax (insert i s) ⟨u,hus,hut⟩
  rw [Finset.card_insert_of_notMem hi] at hc
  omega

/-- Every projection inside the partition unit lies between subset sums whose
cardinalities differ by at most one. This is operator comparison, not a trace
estimate and not an assumed dimension rounding law. -/
theorem exists_subset_rounding
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (E : EquivalentPartition p ι) (q : AlgebraProjection M) (hqp : q ≤ p) :
    ∃ s t : Finset ι, s ⊆ t ∧ t.card ≤ s.card+1 ∧
      (E.subset s).Subequivalent q ∧ q.Subequivalent (E.subset t) ∧
      ∀ a : Finset ι, (E.subset a).Subequivalent q → a.card ≤ s.card := by
  classical
  obtain ⟨s,hs,hmax⟩ := E.exists_maximal_fitting_subset q
  by_cases hsall : s=Finset.univ
  · refine ⟨s,s,Finset.Subset.refl _,Nat.le_succ _,hs,?_,hmax⟩
    rw [hsall,E.subset_univ]
    exact AlgebraProjection.subequivalent_of_le hqp
  · obtain ⟨i,hi⟩ : ∃ i : ι, i ∉ s := by
      by_contra h
      apply hsall
      ext i
      simp only [Finset.mem_univ,iff_true]
      exact Classical.not_not.mp (fun hi => h ⟨i,hi⟩)
    obtain ⟨v,hv,ht⟩ := hs
    let r := AlgebraProjection.remainder v.target q ht
    have hr : r.Subequivalent (E.leg i).target :=
      (AlgebraProjection.subequivalent_total hfactor (E.leg i).target r).resolve_left
        (E.maximal_remainder_not_subequivalent q s hmax v hv ht i hi)
    have hv' : v.target.Equivalent (E.subset s) := ⟨v.adjoint,rfl,v.adjoint_target.trans hv⟩
    have ho := E.subset_mul_piece_of_not_mem s i hi
    have hupper := AlgebraProjection.subequivalent_orthogonalSum
      (AlgebraProjection.remainder_orthogonal v.target q ht) ho hv'.subequivalent hr
    rw [AlgebraProjection.orthogonalSum_remainder] at hupper
    have he : orthogonalSum (E.subset s) (E.leg i).target ho=E.subset (insert i s) :=
      Subtype.ext (E.subset_insert s i hi).symm
    rw [he] at hupper
    exact ⟨s,insert i s,Finset.subset_insert _ _,by rw [Finset.card_insert_of_notMem hi],
      ⟨v,hv,ht⟩,hupper,hmax⟩

end EquivalentPartition

/-! The dyadic lower cut on projections below p and its normalized faithful monotone supremum, capped at one. -/

theorem dyadicWeight_le_one (n : ℕ) (s : Finset (DyadicIndex n)) : dyadicWeight n s ≤ 1 := by
  apply (div_le_one (pow_pos (by norm_num : (0 : ℝ)<2) n)).mpr
  have h : s.card ≤ 2^n := (Finset.card_le_univ s).trans_eq (card_dyadicIndex n)
  exact_mod_cast h

theorem dyadicWeight_children (n : ℕ) (s : Finset (DyadicIndex n)) :
    dyadicWeight (n+1) (s ×ˢ (Finset.univ : Finset Bool))=dyadicWeight n s := by
  change ((s ×ˢ (Finset.univ : Finset Bool)).card : ℝ)/2^(n+1)=(s.card : ℝ)/2^n
  rw [Finset.card_product,Finset.card_univ,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat,pow_succ]
  exact mul_div_mul_right _ _ (by norm_num : (2 : ℝ)≠0)

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

/-- Membership contains an actual partial-isometry witness through Subequivalent. -/
def traceFreeDyadicCut (p q : AlgebraProjection M) : Set ℝ :=
  {x | ∃ n, ∃ s : Finset (DyadicIndex n),
    ((traceFreeDyadicPartition hfactor hdiff p n).subset s).Subequivalent q ∧
      x=dyadicWeight n s}

def traceFreeDyadicSup (p q : AlgebraProjection M) : ℝ :=
  sSup (traceFreeDyadicCut hfactor hdiff p q)

theorem traceFreeDyadicCut_zero_mem (p q : AlgebraProjection M) :
    0 ∈ traceFreeDyadicCut hfactor hdiff p q := by
  refine ⟨0,∅,AlgebraProjection.subequivalent_of_le ?_,?_⟩
  · change q.val*((traceFreeDyadicPartition hfactor hdiff p 0).subset ∅).val=_
    rw [EquivalentPartition.subset_empty,mul_zero]
  · simp only [dyadicWeight,Finset.card_empty,Nat.cast_zero,zero_div]

theorem traceFreeDyadicCut_bddAbove (p q : AlgebraProjection M) :
    BddAbove (traceFreeDyadicCut hfactor hdiff p q) := by
  refine ⟨1,?_⟩
  rintro x ⟨n,s,_,rfl⟩
  exact dyadicWeight_le_one n s

theorem traceFreeDyadicSup_le_one (p q : AlgebraProjection M) :
    traceFreeDyadicSup hfactor hdiff p q ≤ 1 := by
  apply csSup_le ⟨0,traceFreeDyadicCut_zero_mem hfactor hdiff p q⟩
  rintro x ⟨n,s,_,rfl⟩
  exact dyadicWeight_le_one n s

theorem traceFreeDyadicSup_lower_bound (p q : AlgebraProjection M) (n : ℕ)
    (s : Finset (DyadicIndex n))
    (h : ((traceFreeDyadicPartition hfactor hdiff p n).subset s).Subequivalent q) :
    dyadicWeight n s ≤ traceFreeDyadicSup hfactor hdiff p q :=
  le_csSup (traceFreeDyadicCut_bddAbove hfactor hdiff p q) ⟨n,s,h,rfl⟩

theorem traceFreeDyadicCut_mono (p : AlgebraProjection M) {q r : AlgebraProjection M}
    (h : q.Subequivalent r) :
    traceFreeDyadicCut hfactor hdiff p q ⊆ traceFreeDyadicCut hfactor hdiff p r := by
  rintro x ⟨n,s,hs,hx⟩
  exact ⟨n,s,AlgebraProjection.subequivalent_trans hs h,hx⟩

theorem traceFreeDyadicSup_mono (p : AlgebraProjection M) {q r : AlgebraProjection M}
    (h : q.Subequivalent r) :
    traceFreeDyadicSup hfactor hdiff p q ≤ traceFreeDyadicSup hfactor hdiff p r :=
  csSup_le_csSup (traceFreeDyadicCut_bddAbove hfactor hdiff p r)
    ⟨0,traceFreeDyadicCut_zero_mem hfactor hdiff p q⟩
    (traceFreeDyadicCut_mono hfactor hdiff p h)

end

/-! Common refinements compare arbitrary dyadic levels. The supremum takes
the exact dyadic value on every reference subset projection, and finite
rounding bounds every projection with an explicit error at each level. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem dyadicWeight_le_iff (n : ℕ) (s t : Finset (DyadicIndex n)) :
    dyadicWeight n s ≤ dyadicWeight n t ↔ s.card ≤ t.card := by
  unfold dyadicWeight
  rw [div_le_div_iff_of_pos_right (pow_pos (by norm_num : (0 : ℝ)<2) n)]
  exact Nat.cast_le

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

theorem traceFreeDyadic_exists_refined_subset (p : AlgebraProjection M) (n m : ℕ)
    (hnm : n ≤ m) (s : Finset (DyadicIndex n)) :
    ∃ t : Finset (DyadicIndex m),
      (traceFreeDyadicPartition hfactor hdiff p m).subset t=
        (traceFreeDyadicPartition hfactor hdiff p n).subset s ∧
      dyadicWeight m t=dyadicWeight n s := by
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨s,rfl,rfl⟩
  | succ m _ ih =>
    obtain ⟨t,ht,hw⟩ := ih
    refine ⟨t ×ˢ (Finset.univ : Finset Bool),?_,(dyadicWeight_children m t).trans hw⟩
    change ((traceFreeDyadicPartition hfactor hdiff p m).refine _).subset _=_
    rw [EquivalentPartition.subset_refine,ht]

/-- Comparison between any two levels agrees with the real dyadic weights. -/
theorem traceFreeDyadic_comparison_iff_weight
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p : AlgebraProjection M) (hp : p.val≠0) (n m : ℕ)
    (s : Finset (DyadicIndex n)) (t : Finset (DyadicIndex m)) :
    ((traceFreeDyadicPartition hfactor hdiff p n).subset s).Subequivalent
      ((traceFreeDyadicPartition hfactor hdiff p m).subset t) ↔
        dyadicWeight n s ≤ dyadicWeight m t := by
  obtain ⟨s',hs',hws⟩ := traceFreeDyadic_exists_refined_subset hfactor hdiff p n (max n m)
    (le_max_left _ _) s
  obtain ⟨t',ht',hwt⟩ := traceFreeDyadic_exists_refined_subset hfactor hdiff p m (max n m)
    (le_max_right _ _) t
  rw [← hs',← ht',← hws,← hwt]
  rw [EquivalentPartition.subset_subequivalent_iff_card_le hfinite _ hp,dyadicWeight_le_iff]

theorem traceFreeDyadicSup_subset
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p : AlgebraProjection M) (hp : p.val≠0) (n : ℕ) (s : Finset (DyadicIndex n)) :
    traceFreeDyadicSup hfactor hdiff p ((traceFreeDyadicPartition hfactor hdiff p n).subset s)=
      dyadicWeight n s := by
  apply le_antisymm ?_ (traceFreeDyadicSup_lower_bound hfactor hdiff p _ n s
    (AlgebraProjection.subequivalent_refl _))
  apply csSup_le ⟨0,traceFreeDyadicCut_zero_mem hfactor hdiff p _⟩
  rintro x ⟨m,t,h,rfl⟩
  exact (traceFreeDyadic_comparison_iff_weight hfactor hdiff hfinite p hp m n t s).mp h

/-- At every level the cut supremum has actual lower and upper operator
witnesses, with a numerical gap at most 2^(-n). -/
theorem traceFreeDyadicSup_rounding
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p q : AlgebraProjection M) (hp : p.val≠0) (hq : q ≤ p) (n : ℕ) :
    ∃ s t : Finset (DyadicIndex n), s ⊆ t ∧ t.card ≤ s.card+1 ∧
      ((traceFreeDyadicPartition hfactor hdiff p n).subset s).Subequivalent q ∧
      q.Subequivalent ((traceFreeDyadicPartition hfactor hdiff p n).subset t) ∧
      dyadicWeight n s ≤ traceFreeDyadicSup hfactor hdiff p q ∧
      traceFreeDyadicSup hfactor hdiff p q ≤ dyadicWeight n t ∧
      dyadicWeight n t ≤ dyadicWeight n s+1/2^n := by
  obtain ⟨s,t,hst,hcard,hs,ht,_⟩ :=
    (traceFreeDyadicPartition hfactor hdiff p n).exists_subset_rounding hfactor q hq
  refine ⟨s,t,hst,hcard,hs,ht,traceFreeDyadicSup_lower_bound hfactor hdiff p q n s hs,?_,?_⟩
  · have h := traceFreeDyadicSup_mono hfactor hdiff p ht
    rwa [traceFreeDyadicSup_subset hfactor hdiff hfinite p hp] at h
  · change (t.card : ℝ)/2^n ≤ (s.card : ℝ)/2^n+1/2^n
    rw [← add_div]
    apply (div_le_div_iff_of_pos_right (pow_pos (by norm_num : (0 : ℝ)<2) n)).mpr
    exact_mod_cast hcard

end

/-! Orthogonal lower approximants fit disjoint collections of the reference
pieces. Equivalent complements and finite cancellation enforce the capacity. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem subset_complement [DecidableEq ι] (E : EquivalentPartition p ι) (s : Finset ι) :
    E.subset (Finset.univ \ s)=AlgebraProjection.remainder (E.subset s) p (E.subset_le s) := by
  classical
  apply Subtype.ext
  change (∑ i ∈ Finset.univ \ s, (E.leg i).target.val)=p.val-(E.subset s).val
  rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ s),E.total]
  rfl

/-- Two orthogonal fitting projections cannot use more pieces than the unit. -/
theorem orthogonal_fitting_card_bound
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (E : EquivalentPartition p ι) (hp : p.val≠0)
    (q r : AlgebraProjection M) (hqp : q ≤ p) (hrp : r ≤ p) (ho : q.val*r.val=0)
    (s t : Finset ι) (hs : (E.subset s).Subequivalent q) (ht : (E.subset t).Subequivalent r) :
    s.card+t.card ≤ Fintype.card ι := by
  classical
  obtain ⟨v,hv,hvr⟩ := ht
  have hvp := hvr.trans hrp
  have hqv : q.val*v.target.val=0 := projection_orthogonal_of_le ho le_rfl hvr
  have hqr : q ≤ AlgebraProjection.remainder v.target p hvp := by
    change (p.val-v.target.val)*q.val=q.val
    rw [sub_mul,hqp,PartialIsometry.orthogonal_reverse _ _ hqv,sub_zero]
  have he : v.target.Equivalent (E.subset t) := ⟨v.adjoint,rfl,v.adjoint_target.trans hv⟩
  have hc := AlgebraProjection.remainder_equivalent hfinite hfactor hvp (E.subset_le t)
    he (AlgebraProjection.equivalent_refl p)
  rw [← E.subset_complement t] at hc
  have hh : (E.subset s).Subequivalent (E.subset (Finset.univ \ t)) :=
    AlgebraProjection.subequivalent_trans hs (AlgebraProjection.subequivalent_trans
      (AlgebraProjection.subequivalent_of_le hqr) hc.subequivalent)
  have hn := (E.subset_subequivalent_iff_card_le hfinite hp s _).mp hh
  have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ t)
  rw [Finset.card_univ] at hcard
  omega

/-- Disjoint replacement of one collection lets the actual witnesses be added. -/
theorem orthogonal_fitting_union
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (E : EquivalentPartition p ι) (hp : p.val≠0)
    (q r : AlgebraProjection M) (hqp : q ≤ p) (hrp : r ≤ p) (ho : q.val*r.val=0)
    (s t : Finset ι) (hs : (E.subset s).Subequivalent q) (ht : (E.subset t).Subequivalent r) :
    ∃ u : Finset ι, u.card=s.card+t.card ∧
      (E.subset u).Subequivalent (orthogonalSum q r ho) := by
  classical
  obtain ⟨t',hst,hct⟩ := exists_disjoint_card s t
    (E.orthogonal_fitting_card_bound hfinite hfactor hp q r hqp hrp ho s t hs ht)
  have ht' : (E.subset t').Subequivalent r := AlgebraProjection.subequivalent_trans
    (E.subset_equivalent_of_card_eq t' t hct).subequivalent ht
  refine ⟨s ∪ t',by rw [Finset.card_union_of_disjoint hst,hct],?_⟩
  rw [E.subset_union s t' hst]
  exact AlgebraProjection.subequivalent_orthogonalSum
    (E.subset_orthogonal_of_disjoint s t' hst) ho hs ht'

theorem orthogonal_upper_union
    (E : EquivalentPartition p ι) (q r : AlgebraProjection M) (ho : q.val*r.val=0)
    (s t : Finset ι) (hs : q.Subequivalent (E.subset s)) (ht : r.Subequivalent (E.subset t))
    (hcard : s.card+t.card ≤ Fintype.card ι) :
    ∃ u : Finset ι, u.card=s.card+t.card ∧
      (orthogonalSum q r ho).Subequivalent (E.subset u) := by
  classical
  obtain ⟨t',hst,hct⟩ := exists_disjoint_card s t hcard
  have ht' : r.Subequivalent (E.subset t') := AlgebraProjection.subequivalent_trans ht
    (E.subset_equivalent_of_card_eq t t' hct.symm).subequivalent
  refine ⟨s ∪ t',by rw [Finset.card_union_of_disjoint hst,hct],?_⟩
  rw [E.subset_union s t' hst]
  exact AlgebraProjection.subequivalent_orthogonalSum ho
    (E.subset_orthogonal_of_disjoint s t' hst) hs ht'

end EquivalentPartition
end

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
theorem traceFreeDyadicSup_lower_add
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p) (hrp : r ≤ p)
    (ho : q.val*r.val=0) (n : ℕ) (s t : Finset (DyadicIndex n))
    (hs : ((traceFreeDyadicPartition hfactor hdiff p n).subset s).Subequivalent q)
    (ht : ((traceFreeDyadicPartition hfactor hdiff p n).subset t).Subequivalent r) :
    dyadicWeight n s+dyadicWeight n t ≤
      traceFreeDyadicSup hfactor hdiff p (orthogonalSum q r ho) := by
  obtain ⟨u,huc,hu⟩ := (traceFreeDyadicPartition hfactor hdiff p n).orthogonal_fitting_union
    hfinite hfactor hp q r hqp hrp ho s t hs ht
  have h := traceFreeDyadicSup_lower_bound hfactor hdiff p _ n u hu
  simpa only [dyadicWeight,huc,Nat.cast_add,add_div] using h

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

/-- The same constructed lower cut, now normalized at the algebra identity. -/
def traceFreeDimension (q : AlgebraProjection M) : ℝ :=
  traceFreeDyadicSup hfactor hdiff ⟨1,IsStarProjection.one _⟩ q

end Tracial

end

/-! Bounds and concrete dyadic upper approximants for the constructed
projection dimension. These finite estimates do not assume continuity. -/

end Generator

end

end OAI
end


