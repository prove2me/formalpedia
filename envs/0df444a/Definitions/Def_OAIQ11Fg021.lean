-- Prove2me | Definitions.Def_OAIQ11Fg021
-- name    : OAIQ11Fg021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T10:15:32.932838+00:00
-- url     : https://prove2.me/theorems/5cf8fc66-b108-4c19-a8cb-b8ea18782e99
-- title:
--   Definitions bundle OAIQ11Fg021 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 39 declarations of OpenAI's Lean: 39 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_Dimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Dimension.lean), [`FactorGeneration_DyadicComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/DyadicComparison.lean), [`FactorGeneration_SpectralDimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralDimension.lean).
--
--   **Imports.** It imports the bundle `OAIQ11Fg020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg015`, `OAIQ11Fg016`, `OAIQ11Fg025` and `OAIQ11Fg027`; the proofs of `OAI_Generator_Tracial_exists_admissible_family_patch`, `OAI_Generator_Tracial_exists_irreducible_corner_local_piece` and `OAI_Generator_Tracial_representedCorner_diffuse`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ11Fg020

section
-- module Solutions.OAIQ11_FG.FactorGeneration_DyadicComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

/-- Subset sums stay compatible with refinement to all children. -/
theorem subset_refine {κ : Type*} [Fintype κ] (E : EquivalentPartition p ι)
    (F : EquivalentPartition E.base κ) (s : Finset ι) :
    (E.refine F).subset (s ×ˢ Finset.univ)=E.subset s := by
  apply Subtype.ext
  rw [subset_val,Finset.sum_product]
  exact Finset.sum_congr rfl (fun i _ => E.refine_parent F i)

/-! Exact finite cardinal comparison of sums of equivalent nonzero projections.
Finiteness prevents a larger collection from embedding in a smaller one. -/

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
-- module Solutions.OAIQ11_FG.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

theorem traceFreeDyadicCut_zero_mem (p q : AlgebraProjection M) :
    0 ∈ traceFreeDyadicCut hfactor hdiff p q := by
  refine ⟨0,∅,AlgebraProjection.subequivalent_of_le ?_,?_⟩
  · change q.val*((traceFreeDyadicPartition hfactor hdiff p 0).subset ∅).val=_
    rw [EquivalentPartition.subset_empty,mul_zero]
  · simp only [dyadicWeight,Finset.card_empty,Nat.cast_zero,zero_div]

theorem traceFreeDyadicSup_nonneg (p q : AlgebraProjection M) :
    0 ≤ traceFreeDyadicSup hfactor hdiff p q :=
  le_csSup (traceFreeDyadicCut_bddAbove hfactor hdiff p q)
    (traceFreeDyadicCut_zero_mem hfactor hdiff p q)

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

theorem traceFreeDyadicSup_equivalent (p : AlgebraProjection M) {q r : AlgebraProjection M}
    (h : q.Equivalent r) :
    traceFreeDyadicSup hfactor hdiff p q=traceFreeDyadicSup hfactor hdiff p r :=
  le_antisymm (traceFreeDyadicSup_mono hfactor hdiff p h.subequivalent)
    (traceFreeDyadicSup_mono hfactor hdiff p (AlgebraProjection.equivalent_symm h).subequivalent)

theorem traceFreeDyadicSup_zero (p q : AlgebraProjection M) (hp : p.val≠0) (hq : q.val=0) :
    traceFreeDyadicSup hfactor hdiff p q=0 := by
  apply le_antisymm ?_ (traceFreeDyadicSup_nonneg hfactor hdiff p q)
  apply csSup_le ⟨0,traceFreeDyadicCut_zero_mem hfactor hdiff p q⟩
  rintro x ⟨n,s,⟨v,hv,ht⟩,rfl⟩
  have htz : v.target.val=0 := by
    change q.val*v.target.val=v.target.val at ht
    rw [hq,zero_mul] at ht
    exact ht.symm
  have hvz : v.val=0 := by
    have h := v.target_mul
    rw [htz,zero_mul] at h
    exact h.symm
  have hsz : ((traceFreeDyadicPartition hfactor hdiff p n).subset s).val=0 := by
    rw [← hv,← v.initial,hvz,star_zero,zero_mul]
  have hs : s ⊆ ∅ :=
    ((traceFreeDyadicPartition hfactor hdiff p n).subset_le_subset_iff hp s ∅).mp (by
      change ((traceFreeDyadicPartition hfactor hdiff p n).subset ∅).val*
        ((traceFreeDyadicPartition hfactor hdiff p n).subset s).val=_
      rw [hsz,mul_zero])
  have he : s=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => Finset.notMem_empty i (hs hi))
  simp only [he,dyadicWeight,Finset.card_empty,Nat.cast_zero,zero_div,le_refl]

end

/-! Common refinements compare arbitrary dyadic levels. The supremum takes
the exact dyadic value on every reference subset projection, and finite
rounding bounds every projection with an explicit error at each level. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

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

include hfinite in
theorem traceFreeDyadicSup_upper_add
    (p q r : AlgebraProjection M) (hp : p.val≠0) (ho : q.val*r.val=0)
    (n : ℕ) (s t : Finset (DyadicIndex n))
    (hs : q.Subequivalent ((traceFreeDyadicPartition hfactor hdiff p n).subset s))
    (ht : r.Subequivalent ((traceFreeDyadicPartition hfactor hdiff p n).subset t)) :
    traceFreeDyadicSup hfactor hdiff p (orthogonalSum q r ho) ≤
      dyadicWeight n s+dyadicWeight n t := by
  by_cases hc : s.card+t.card ≤ Fintype.card (DyadicIndex n)
  · obtain ⟨u,huc,hu⟩ := (traceFreeDyadicPartition hfactor hdiff p n).orthogonal_upper_union
      q r ho s t hs ht hc
    have h := traceFreeDyadicSup_mono hfactor hdiff p hu
    rw [traceFreeDyadicSup_subset hfactor hdiff hfinite p hp] at h
    simpa only [dyadicWeight,huc,Nat.cast_add,add_div] using h
  · apply le_trans (traceFreeDyadicSup_le_one hfactor hdiff p _)
    have hn : 2^n ≤ s.card+t.card := by rw [card_dyadicIndex] at hc; omega
    change 1 ≤ (s.card : ℝ)/2^n+(t.card : ℝ)/2^n
    rw [← add_div]
    apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ)<2) n)).mpr
    simp only [one_mul]
    exact_mod_cast hn

include hfinite in
/-- The dyadic supremum is additive on actual orthogonal projections below p. -/
theorem traceFreeDyadicSup_orthogonal_add
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p) (hrp : r ≤ p)
    (ho : q.val*r.val=0) :
    traceFreeDyadicSup hfactor hdiff p (orthogonalSum q r ho)=
      traceFreeDyadicSup hfactor hdiff p q+traceFreeDyadicSup hfactor hdiff p r := by
  apply eq_of_all_dyadic_errors
  intro n
  obtain ⟨s,t,_,_,hs,ht,hql,hqu,hqe⟩ :=
    traceFreeDyadicSup_rounding hfactor hdiff hfinite p q hp hqp n
  obtain ⟨a,b,_,_,ha,hb,hrl,hru,hre⟩ :=
    traceFreeDyadicSup_rounding hfactor hdiff hfinite p r hp hrp n
  have hlo := traceFreeDyadicSup_lower_add hfactor hdiff hfinite p q r hp hqp hrp ho n s a hs ha
  have hhi := traceFreeDyadicSup_upper_add hfactor hdiff hfinite p q r hp ho n t b ht hb
  rw [show (2 : ℝ)/2^n=2*(1/2^n) by ring]
  apply abs_le.mpr
  constructor <;> linarith

end Tracial

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

theorem traceFreeDimension_nonneg (q : AlgebraProjection M) :
    0 ≤ traceFreeDimension hfactor hdiff q :=
  traceFreeDyadicSup_nonneg hfactor hdiff _ q

theorem traceFreeDimension_le_one (q : AlgebraProjection M) :
    traceFreeDimension hfactor hdiff q ≤ 1 :=
  traceFreeDyadicSup_le_one hfactor hdiff _ q

theorem traceFreeDimension_subequivalent {q r : AlgebraProjection M}
    (h : q.Subequivalent r) :
    traceFreeDimension hfactor hdiff q ≤ traceFreeDimension hfactor hdiff r :=
  traceFreeDyadicSup_mono hfactor hdiff _ h

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralDimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite spectral weights of the constructed projection dimension obey an
operator-norm bound. No linear trace on noncommuting elements is assumed. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_finsetSum
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} (q : I → AlgebraProjection M) (s : Finset I)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i≠j → (q i).val*(q j).val=0) :
    traceFreeDimension hfactor hdiff (AlgebraProjection.finsetSum q s ho)=
      ∑ i ∈ s, traceFreeDimension hfactor hdiff (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz : (AlgebraProjection.finsetSum q ∅ ho).val=0 := by simp [AlgebraProjection.finsetSum]
    simpa only [Finset.sum_empty,traceFreeDimension] using traceFreeDyadicSup_zero hfactor hdiff
      ⟨1,IsStarProjection.one _⟩ _ hunit hz
  | @insert i s hi ih =>
    have hos : ∀ j ∈ s, ∀ k ∈ s, j≠k → (q j).val*(q k).val=0 :=
      fun j hj k hk => ho j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    let r := AlgebraProjection.finsetSum q s hos
    have hqr : (q i).val*r.val=0 := by
      change (q i).val*(∑ j ∈ s, (q j).val)=0
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero (fun j hj => ho i (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (fun he => hi (he.symm ▸ hj)))
    have he : AlgebraProjection.finsetSum q (insert i s) ho=orthogonalSum (q i) r hqr := by
      apply Subtype.ext
      exact Finset.sum_insert hi
    rw [he,Finset.sum_insert hi]
    have hadd := traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ (q i) r hunit (one_mul _) (one_mul _) hqr
    change traceFreeDimension hfactor hdiff (orthogonalSum (q i) r hqr)=
      traceFreeDimension hfactor hdiff (q i)+traceFreeDimension hfactor hdiff r at hadd
    rw [hadd,ih hos]

include hfinite in
theorem traceFreeDimension_sum_of_total
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Fintype I] (q : I → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0)
    (p : AlgebraProjection M) (hp : ∑ i, (q i).val=p.val) :
    ∑ i, traceFreeDimension hfactor hdiff (q i)=traceFreeDimension hfactor hdiff p := by
  classical
  have he : AlgebraProjection.finsetSum q Finset.univ (fun i _ j _ => ho i j)=p := Subtype.ext hp
  rw [← he]
  exact (traceFreeDimension_finsetSum hfactor hdiff hfinite hunit q Finset.univ _).symm

include hfinite in
/-- A finite orthogonal spectral value has the required operator-norm bound. -/
theorem traceFreeDimension_spectralWeight_norm_le
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Fintype I] (q : I → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0) (c : I → ℂ) :
    ‖∑ i, c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ ≤
      ‖∑ i, c i • (q i).val‖ := by
  classical
  let a : M.toStarSubalgebra := ∑ i, c i • (q i).val
  have hpiece (i : I) : a*(q i).val=c i • (q i).val := by
    dsimp [a]
    rw [Finset.sum_mul]
    apply (Finset.sum_eq_single i ?_ ?_).trans
      (by rw [smul_mul_assoc,(q i).property.isIdempotentElem.eq])
    · intro j _ hji
      rw [smul_mul_assoc,ho j i hji,smul_zero]
    · intro h; exact (h (Finset.mem_univ i)).elim
  have hterm (i : I) : ‖c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ ≤
      ‖a‖*traceFreeDimension hfactor hdiff (q i) := by
    by_cases hz : (q i).val=0
    · have hD := traceFreeDyadicSup_zero hfactor hdiff ⟨1,IsStarProjection.one _⟩ (q i) hunit hz
      change traceFreeDimension hfactor hdiff (q i)=0 at hD
      simp only [hD,Complex.ofReal_zero,mul_zero,norm_zero,le_refl]
    · have hnorm := norm_mul_le a (q i).val
      rw [hpiece i,norm_smul] at hnorm
      have hpos : 0 < ‖(q i).val‖ := norm_pos_iff.mpr hz
      have hci : ‖c i‖ ≤ ‖a‖ := by nlinarith
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (traceFreeDimension_nonneg hfactor hdiff _)]
      exact mul_le_mul_of_nonneg_right hci (traceFreeDimension_nonneg hfactor hdiff _)
  have hdim : (∑ i, traceFreeDimension hfactor hdiff (q i)) ≤ 1 := by
    rw [← traceFreeDimension_finsetSum hfactor hdiff hfinite hunit q Finset.univ
      (fun i _ j _ => ho i j)]
    exact traceFreeDimension_le_one hfactor hdiff _
  calc
    ‖∑ i, c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ ≤
        ∑ i, ‖c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖a‖*traceFreeDimension hfactor hdiff (q i) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = ‖a‖*(∑ i, traceFreeDimension hfactor hdiff (q i)) := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖a‖ := by nlinarith [norm_nonneg a]

include hfinite in
/-- In a fixed orthogonal partition, the spectral-value map is contractive. -/
theorem traceFreeDimension_spectralWeight_sub_norm_le
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Fintype I] (q : I → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0) (c d : I → ℂ) :
    ‖(∑ i, c i*(traceFreeDimension hfactor hdiff (q i) : ℂ))-
      (∑ i, d i*(traceFreeDimension hfactor hdiff (q i) : ℂ))‖ ≤
      ‖(∑ i, c i • (q i).val)-(∑ i, d i • (q i).val)‖ := by
  simpa only [sub_mul,sub_smul,Finset.sum_sub_distrib] using
    traceFreeDimension_spectralWeight_norm_le hfactor hdiff hfinite hunit q ho (fun i => c i-d i)

/-! Spectral dimension weights agree under common commuting refinements.
Contractivity is proved for two commuting partitions, not noncommuting inputs. -/
namespace CornerPartition
variable {p : AlgebraProjection M} (Q R : CornerPartition p)
variable (hc : ∀ i j, Commute (Q.piece i).val (R.piece j).val)

include hfinite in
theorem dimension_joint_row (hunit : (1 : M.toStarSubalgebra) ≠ 0) (i : Fin Q.size) :
    ∑ j, traceFreeDimension hfactor hdiff (Q.jointPiece R hc (i,j))=
      traceFreeDimension hfactor hdiff (Q.piece i) := by
  apply traceFreeDimension_sum_of_total hfactor hdiff hfinite hunit
    (fun j => Q.jointPiece R hc (i,j))
    (fun j k hjk => Q.jointPiece_orthogonal R hc (i,j) (i,k) (fun h => hjk (congrArg Prod.snd h)))
  change (∑ j, (Q.piece i).val*(R.piece j).val)=(Q.piece i).val
  rw [← Finset.mul_sum,R.total,projection_mul_of_le (Q.piece_le i)]

include hfinite in
theorem dimension_joint_column (hunit : (1 : M.toStarSubalgebra) ≠ 0) (j : Fin R.size) :
    ∑ i, traceFreeDimension hfactor hdiff (Q.jointPiece R hc (i,j))=
      traceFreeDimension hfactor hdiff (R.piece j) := by
  apply traceFreeDimension_sum_of_total hfactor hdiff hfinite hunit
    (fun i => Q.jointPiece R hc (i,j))
    (fun i k hik => Q.jointPiece_orthogonal R hc (i,j) (k,j) (fun h => hik (congrArg Prod.fst h)))
  change (∑ i, (Q.piece i).val*(R.piece j).val)=(R.piece j).val
  rw [← Finset.sum_mul,Q.total]
  exact R.piece_le j

include hfinite in
theorem dimension_weight_joint_left (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : Fin Q.size → ℂ) :
    (∑ a : Fin Q.size × Fin R.size,
      c a.1*(traceFreeDimension hfactor hdiff (Q.jointPiece R hc a) : ℂ))=
        ∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [← Finset.mul_sum,← Complex.ofReal_sum,dimension_joint_row hfactor hdiff hfinite Q R hc hunit]

include hfinite in
theorem dimension_weight_joint_right (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : Fin R.size → ℂ) :
    (∑ a : Fin Q.size × Fin R.size,
      c a.2*(traceFreeDimension hfactor hdiff (Q.jointPiece R hc a) : ℂ))=
        ∑ i, c i*(traceFreeDimension hfactor hdiff (R.piece i) : ℂ) := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [← Finset.mul_sum,← Complex.ofReal_sum,dimension_joint_column hfactor hdiff hfinite Q R hc hunit]

include hfinite hc in
/-- Changing between two commuting partitions preserves the norm estimate. -/
theorem dimension_weight_cross_norm_le (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : Fin Q.size → ℂ) (d : Fin R.size → ℂ) :
    ‖(∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))-
      (∑ j, d j*(traceFreeDimension hfactor hdiff (R.piece j) : ℂ))‖ ≤
      ‖(∑ i, c i • (Q.piece i).val)-(∑ j, d j • (R.piece j).val)‖ := by
  have h := traceFreeDimension_spectralWeight_sub_norm_le hfactor hdiff hfinite hunit
    (Q.jointPiece R hc) (Q.jointPiece_orthogonal R hc) (fun a => c a.1) (fun a => d a.2)
  rwa [Q.dimension_weight_joint_left hfactor hdiff hfinite R hc hunit c,
    Q.dimension_weight_joint_right hfactor hdiff hfinite R hc hunit d,
    Q.joint_sum_left R hc c,Q.joint_sum_right R hc d] at h

end CornerPartition

end

/-! Construct the unique real spectral dimension value of each self-adjoint
operator by norm approximation. Global noncommuting additivity is not asserted. -/

/-! The constructed spectral value is bounded and extends the actual
projection dimension. These laws do not assert noncommuting additivity. -/

/-! Finite-family tests and real homogeneity for the constructed spectral value.
These statements do not assert additivity for noncommuting operators. -/
open scoped BigOperators

end Generator.Tracial

end

end OAI
end


