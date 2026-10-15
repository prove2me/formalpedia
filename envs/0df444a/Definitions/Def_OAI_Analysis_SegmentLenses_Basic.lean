-- Prove2me | Definitions.Def_OAI_Analysis_SegmentLenses_Basic
-- name    : OAI_Analysis_SegmentLenses_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:52:31.6341+00:00
-- url     : https://prove2.me/theorems/81454adb-f9d1-478d-ac3b-2b050765132a
-- title:
--   Segment-test seminorms: column bounds, the square formula and disjoint-segment lower bounds
-- statement:
--   Let $V$ be a set with a *segment system*, i.e. a distinguished class of finite subsets of $V$, called segments, that contains every singleton $\{v\}$. A *segment family* $\mathcal F$ is a finite set of pairwise disjoint segments. For a finitely supported $u:V\to\mathbb{R}$ the family $\mathcal F$ gives a test vector and a family seminorm:
--   $$
--   T_{\mathcal F}u=\Big(\sum_{v\in S}u(v)\Big)_{S\in\mathcal F}\in\ell_2(\mathcal F),\qquad p_{\mathcal F}(u)=\|T_{\mathcal F}u\|_2 .
--   $$
--   The segment seminorm $\|u\|_{\mathrm{seg}}$ is the supremum of all the $p_{\mathcal F}$. These objects are fixed in the base definitions. This file establishes their elementary properties.
--
--   1. **Default family.** The empty family is the default segment family.
--   2. **Columns and test values.** The column $T_{\mathcal F}\delta_v=(\mathbf 1[v\in S])_{S\in\mathcal F}$ has Euclidean norm at most $1$. By disjointness it is either a standard basis vector of $\ell_2(\mathcal F)$ or zero. The $S$-coordinate of $T_{\mathcal F}u$ is $\sum_{v\in S}u(v)$, and $\|T_{\mathcal F}u\|_2\le\sum_{v}|u(v)|$.
--   3. **Square formula.** For every family,
--   $$
--   p_{\mathcal F}(u)^2=\sum_{S\in\mathcal F}\Big(\sum_{v\in S}u(v)\Big)^2 .
--   $$
--   For the one-member family $\{\{v\}\}$ this gives $p_{\{\{v\}\}}(u)=|u(v)|$.
--   4. **Supremum formula.** The family seminorms are bounded above, with the $\ell_1$ norm as a common bound. Hence $\|u\|_{\mathrm{seg}}=\sup_{\mathcal F}p_{\mathcal F}(u)$ pointwise, $p_{\mathcal F}(u)\le\|u\|_{\mathrm{seg}}$ for every family $\mathcal F$, and $|u(v)|\le\|u\|_{\mathrm{seg}}$ for every $v\in V$.
--   5. **Indexed test bound.** Let $\iota$ be a finite index set and let $(S_i)_{i\in\iota}$ be pairwise disjoint finite subsets of $V$, each of which is empty or a segment. Then
--   $$
--   \sum_{i\in\iota}\Big(\sum_{v\in S_i}u(v)\Big)^2\le\|u\|_{\mathrm{seg}}^2 .
--   $$
--   6. **Ancestry relations.** Two finite words over $\mathbb{N}$ that are prefixes of each other are equal. On the forest vertices, i.e. the pairs $(n,w)$ with $n\ge1$ and $w$ a word of length at most $n$, the ancestor relation is defined by: $(n,w)$ is an ancestor of $(m,w')$ iff $n=m$ and $w$ is a prefix of $w'$. This relation is reflexive and antisymmetric.
--
--   The coordinate bound $|u(v)|\le\|u\|_{\mathrm{seg}}$ makes the segment seminorm a genuine norm. The indexed test bound is the basic way to estimate it from below: every disjoint arrangement of segments yields a lower bound for $\|u\|_{\mathrm{seg}}^2$.
--
--   **Formalization Note** Finitely supported functions are `V →₀ ℝ`, and the segment seminorm `segmentSeminorm V` is the supremum `⨆ F, F.seminorm` in the lattice of seminorms. `segmentTests_bdd` and `segmentSeminorm_apply` show that this supremum is computed pointwise. The phrase "empty or a segment" appears because the segment predicate is not assumed to hold for the empty set. The lemmas are `norm_column_le`, `test_apply`, `norm_test_le`, `seminorm_sq`, `singleton_seminorm`, `le_segmentSeminorm`, `abs_coord_le`, `indexed_test_bound`, `prefix_antisymm`, `forestAncestor_refl` and `forestAncestor_antisymm`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MidpointLenses mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MidpointLenses

namespace OAI

/-!
# Segment tests, their completion, and coordinate functionals
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

namespace SegmentFamily
variable {V : Type*} [SegmentSystem V]

instance : Inhabited (SegmentFamily V) := ⟨⟨∅, by simp, by simp⟩⟩

theorem norm_column_le (F : SegmentFamily V) (v : V) : ‖F.column v‖ ≤ 1 := by
  classical
  by_cases hv : ∃ S ∈ F.sets, v ∈ S
  · obtain ⟨S, hS, hvS⟩ := hv
    have he : F.column v = PiLp.single 2 (⟨S, hS⟩ : F.sets) (1 : ℝ) := by
      ext T
      change (if v ∈ T.val then (1 : ℝ) else 0) = _
      by_cases hTS : T = ⟨S, hS⟩
      · subst T
        simp [hvS]
      · have hn : v ∉ T.val := by
          intro hvT
          have hne : T.val ≠ S := fun h => hTS (Subtype.ext h)
          exact Finset.disjoint_left.mp (F.disjoint T.property hS hne) hvT hvS
        simp [hTS, hn]
    rw [he, PiLp.norm_single]
    norm_num
  · have he : F.column v = 0 := by
      ext S
      have hn : v ∉ S.val := fun h => hv ⟨S.val, S.property, h⟩
      simp [column, hn]
    rw [he, norm_zero]
    norm_num

theorem test_apply (F : SegmentFamily V) (u : V →₀ ℝ) (S : F.sets) :
    F.test u S = ∑ v ∈ S.val, u v := by
  classical
  simp only [test, Finsupp.linearCombination_apply, Finsupp.sum,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, column,
    smul_eq_mul]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro v hv hnv
    have hnot : v ∉ u.support := by
      intro hvs
      exact hnv (Finset.mem_filter.mpr ⟨hvs, hv⟩)
    exact Finsupp.notMem_support_iff.mp hnot

theorem norm_test_le (F : SegmentFamily V) (u : V →₀ ℝ) :
    ‖F.test u‖ ≤ ∑ v ∈ u.support, |u v| := by
  classical
  rw [test, Finsupp.linearCombination_apply, Finsupp.sum]
  calc
    ‖∑ v ∈ u.support, u v • F.column v‖ ≤
        ∑ v ∈ u.support, ‖u v • F.column v‖ := norm_sum_le _ _
    _ ≤ ∑ v ∈ u.support, |u v| := by
      apply Finset.sum_le_sum
      intro v hv
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (F.norm_column_le v)

theorem seminorm_sq (F : SegmentFamily V) (u : V →₀ ℝ) :
    F.seminorm u ^ 2 = ∑ S : F.sets, (∑ v ∈ S.val, u v) ^ 2 := by
  change ‖F.test u‖ ^ 2 = _
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [F.test_apply]

theorem singleton_seminorm (v : V) (u : V →₀ ℝ) :
    (singleton v).seminorm u = |u v| := by
  have h := (singleton v).seminorm_sq u
  have hh : (∑ S : (singleton v).sets, (∑ w ∈ S.val, u w) ^ 2) = u v ^ 2 := by
    exact (Finset.sum_coe_sort (singleton v).sets
      (fun S : Finset V => (∑ w ∈ S, u w) ^ 2)).trans (by simp [singleton])
  rw [hh] at h
  have hn := apply_nonneg (singleton v).seminorm u
  nlinarith [sq_abs (u v), abs_nonneg (u v)]

end SegmentFamily

theorem segmentTests_bdd (V : Type*) [SegmentSystem V] :
    BddAbove (Set.range (SegmentFamily.seminorm (V := V))) := by
  rw [Seminorm.bddAbove_iff]
  refine ⟨fun u => ∑ v ∈ u.support, |u v|, ?_⟩
  rintro _ ⟨p, ⟨F, rfl⟩, rfl⟩ u
  exact F.norm_test_le u

theorem segmentSeminorm_apply {V : Type*} [SegmentSystem V] (u : V →₀ ℝ) :
    segmentSeminorm V u = ⨆ F : SegmentFamily V, F.seminorm u :=
  Seminorm.iSup_apply (segmentTests_bdd V)

theorem le_segmentSeminorm {V : Type*} [SegmentSystem V]
    (F : SegmentFamily V) (u : V →₀ ℝ) : F.seminorm u ≤ segmentSeminorm V u := by
  have h := le_ciSup (f := fun G : SegmentFamily V => G.seminorm) (segmentTests_bdd V) F
  exact Seminorm.le_def.mp h u

theorem abs_coord_le {V : Type*} [SegmentSystem V] (u : V →₀ ℝ) (v : V) :
    |u v| ≤ segmentSeminorm V u := by
  rw [← SegmentFamily.singleton_seminorm v u]
  exact le_segmentSeminorm _ _

theorem indexed_test_bound {V ι : Type*} [SegmentSystem V] [Fintype ι]
    (u : V →₀ ℝ) (S : ι → Finset V)
    (hS : ∀ i, S i = ∅ ∨ SegmentSystem.isSegment (S i))
    (hd : Pairwise fun i j => Disjoint (S i) (S j)) :
    ∑ i, (∑ v ∈ S i, u v) ^ 2 ≤ segmentSeminorm V u ^ 2 := by
  classical
  let F : SegmentFamily V :=
    { sets := (Finset.univ.image S).erase ∅
      segment := by
        intro T hT
        obtain ⟨hne, him⟩ := Finset.mem_erase.mp hT
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp him
        exact (hS i).resolve_left hne
      disjoint := by
        intro A hA B hB hne
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hA).2
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hB).2
        exact hd (fun hij => hne (congrArg S hij)) }
  have he : F.seminorm u ^ 2 = ∑ i, (∑ v ∈ S i, u v) ^ 2 := by
    rw [F.seminorm_sq]
    rw [Finset.sum_coe_sort F.sets (fun T : Finset V => (∑ v ∈ T, u v) ^ 2)]
    change (∑ T ∈ (Finset.univ.image S).erase ∅, (∑ v ∈ T, u v) ^ 2) = _
    rw [Finset.sum_erase _ (by simp)]
    apply Finset.sum_image_of_pairwise_eq_zero
    intro i hi j hj hij heq
    have hempty : S i = ∅ := by
      have hh : Disjoint (S i) (S j) := hd hij
      rw [← heq] at hh
      exact disjoint_self.mp hh
    simp [hempty]
  rw [← he]
  exact (sq_le_sq₀ (apply_nonneg F.seminorm u)
    (apply_nonneg (segmentSeminorm V) u)).mpr (le_segmentSeminorm F u)

namespace Test
variable {V : Type*}
variable [SegmentSystem V]
end Test

theorem prefix_antisymm {a b : List ℕ}
    (hab : a.IsPrefix b) (hba : b.IsPrefix a) : a = b :=
  hab.eq_of_length (Nat.le_antisymm hab.length_le hba.length_le)

theorem forestAncestor_refl (v : ForestVertex) : ForestAncestor v v :=
  ⟨rfl, List.prefix_rfl⟩

theorem forestAncestor_antisymm {a b : ForestVertex}
    (hab : ForestAncestor a b) (hba : ForestAncestor b a) : a = b := by
  apply Subtype.ext
  exact Prod.ext hab.1 (prefix_antisymm hab.2 hba.2)

end SegmentLenses

end

end OAI


