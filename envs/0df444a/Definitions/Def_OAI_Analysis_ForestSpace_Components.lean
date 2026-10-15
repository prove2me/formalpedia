-- Prove2me | Definitions.Def_OAI_Analysis_ForestSpace_Components
-- name    : OAI_Analysis_ForestSpace_Components
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:04:58.698345+00:00
-- url     : https://prove2.me/theorems/833b5c2b-119a-4691-ac95-32faaf0bb462
-- title:
--   Height components of the forest and reflexivity of its segment-norm completion
-- statement:
--   Let $V$ be a partially ordered set. A *segment* of $V$ is a finite set $S\subseteq V$ that is a chain and is order-convex ($a,b\in S$ and $a\le c\le b$ imply $c\in S$). For a finitely supported $u:V\to\mathbb{R}$ write $u(S)=\sum_{v\in S}u(v)$; the *disjoint-segment norm* is
--   $$
--   \|u\|=\Bigl(\sup\Bigl\{\sum_{i\in I}u(S_i)^2\ :\ (S_i)_{i\in I}\ \text{a finite family of pairwise disjoint segments}\Bigr\}\Bigr)^{1/2},
--   $$
--   and $J(V)$ is the completion of the space $c_{00}(V)$ of finitely supported functions under this norm.
--
--   The forest $\mathcal F$ consists of the pairs $(h,w)$ with $h\ge1$ and $w$ a finite word over $\mathbb{N}$ of length at most $h$, ordered by $(h,w)\le(h',w')$ iff $h=h'$ and $w$ is a prefix of $w'$. For $h\in\mathbb{N}$ the *height-$h$ component* $T_h=\{(h',w)\in\mathcal F:\ h'=h\}$ is a copy of the tree of words of length at most $h$ (and $T_0=\varnothing$). Points of different components are incomparable, so every segment of $\mathcal F$ lies in a single component. The file defines:
--
--   1. **Component restriction.** For $h\in\mathbb{N}$, the linear map $c_{00}(\mathcal F)\to c_{00}(T_h)$, $u\mapsto u|_{T_h}$.
--   2. **Extension by zero.** For $h\in\mathbb{N}$, the map $c_{00}(T_h)\to c_{00}(\mathcal F)$ that extends $u$ by $0$ outside $T_h$. Restricting the extension back to $T_h$ returns $u$, and restricting it to $T_j$ with $j\ne h$ gives $0$.
--   3. **Component support.** For $u\in c_{00}(\mathcal F)$, the finite set of heights $h$ of the points $(h,w)$ at which $u$ is nonzero; $u|_{T_h}=0$ for every $h$ outside it.
--   4. **Component decomposition.** The bounded linear operator
--   $$
--   D:\ c_{00}(\mathcal F)\longrightarrow\Bigl(\bigoplus_{h\in\mathbb{N}}J(T_h)\Bigr)_{\ell^2},\qquad Du=\bigl(u|_{T_h}\bigr)_{h\in\mathbb{N}},
--   $$
--   into the $\ell^2$-sum of the completions $J(T_h)$, normed by $\|(x_h)_h\|=\bigl(\sum_h\|x_h\|^2\bigr)^{1/2}$. Only finitely many coordinates of $Du$ are nonzero and $\|Du\|^2=\sum_h\|u|_{T_h}\|^2$.
--
--   The file proves that $\|u\|\le\|Du\|\le2\|u\|$ for all $u\in c_{00}(\mathcal F)$ (in fact $\|Du\|^2\le2\|u\|^2$) and that $D$ has dense range, so $D$ extends to an isomorphism of Banach spaces between $J(\mathcal F)$ and the $\ell^2$-sum. Each $J(T_h)$ is reflexive (a segment of $T_h$ has at most $h+1$ points), and an $\ell^2$-sum of reflexive spaces is reflexive; the file concludes that $J(\mathcal F)$ is reflexive, i.e. its canonical embedding into the bidual is surjective. It also records, for an arbitrary partially ordered set $W$ and $u\in c_{00}(W)$, a *half-norming test*: a finite family $(S_i)$ of pairwise disjoint segments of $W$ with
--   $$
--   \|u\|^2\le2\sum_i u(S_i)^2 .
--   $$
--
--   Reflexivity of $J(\mathcal F)$ is the input that later identifies the closed span of the coordinate functionals with the full dual $J(\mathcal F)^*$ and gives the reflexivity of that dual.
--
--   **Formalization Note** Components are the subtypes `Component h` of `Vertex` cut out by `v.height = h`, finitely supported functions are `TestVector`, and $J$ is `UniformSpace.Completion`. The operator is `rawDecomposition`, obtained from the linear map `rawDecompositionLinear` by `mkContinuous` with the bound $2$; the half-norming test is `exists_half_test` and reflexivity is `reflexive_forest_J`. The remaining members (segments of a component versus segments of the forest, segment sums of restrictions, two local `ite` aliases) are bookkeeping lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Components.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Components.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForestSpace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections
import Definitions.Def_OAI_Analysis_ForestSpace_Renorming
import Definitions.Def_OAI_Analysis_ForestSpace_Coordinates
import Definitions.Def_OAI_Analysis_ForestSpace_Trees
import Definitions.Def_OAI_Analysis_ForestSpace_Reflexivity

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section ComponentDecomposition

noncomputable def componentRaw (h : ℕ) : TestVector Vertex →ₗ[ℝ] TestVector (Component h) where
  toFun u := u.toFinsupp.subtypeDomain (fun v => v.height = h)
  map_add' u v := by ext w; rfl
  map_smul' a u := by ext w; rfl

@[simp] theorem componentRaw_apply (h : ℕ) (u : TestVector Vertex) (v : Component h) :
    componentRaw h u v = u v := rfl

noncomputable def liftComponent (h : ℕ) (u : TestVector (Component h)) : TestVector Vertex :=
  Finsupp.extendDomain u.toFinsupp

@[simp] theorem liftComponent_apply (h : ℕ) (u : TestVector (Component h)) (v : Vertex) :
    liftComponent h u v = if hv : v.height = h then u ⟨v,hv⟩ else 0 :=
  Finsupp.extendDomain_apply _ _

@[simp] theorem componentRaw_lift_same (h : ℕ) (u : TestVector (Component h)) :
    componentRaw h (liftComponent h u) = u := by
  ext v
  simp [v.property]

 theorem componentRaw_lift_other (h j : ℕ) (hj : j ≠ h) (u : TestVector (Component h)) :
    componentRaw j (liftComponent h u) = 0 := by
  ext v
  have hv : v.val.height ≠ h := by simpa only [v.property] using hj
  simp [hv]

noncomputable def componentSupport (u : TestVector Vertex) : Finset ℕ :=
  u.toFinsupp.support.image Vertex.height

 theorem componentRaw_zero (u : TestVector Vertex) {h : ℕ} (hh : h ∉ componentSupport u) :
    componentRaw h u = 0 := by
  ext v
  change u v = 0
  apply Finsupp.notMem_support_iff.mp
  intro hv
  exact hh (Finset.mem_image.mpr ⟨v,hv,v.property⟩)

noncomputable def rawDecompositionLinear : TestVector Vertex →ₗ[ℝ] lp (fun h => J (Component h)) 2 where
  toFun u := ⟨(fun h => (componentRaw h u : J (Component h))),memℓp_gen (by
    apply summable_of_ne_finset_zero (s := componentSupport u)
    intro h hh
    simp [componentRaw_zero u hh])⟩
  map_add' u v := by
    ext h
    change ((componentRaw h (u+v) : TestVector (Component h)) : J (Component h)) = _
    rw [map_add,UniformSpace.Completion.coe_add]
    rfl
  map_smul' a u := by
    ext h
    change ((componentRaw h (a • u) : TestVector (Component h)) : J (Component h)) = _
    rw [map_smul,UniformSpace.Completion.coe_smul]
    rfl

@[simp] theorem rawDecomposition_apply (u : TestVector Vertex) (h : ℕ) :
    rawDecompositionLinear u h = (componentRaw h u : J (Component h)) := rfl

 theorem rawDecomposition_norm_sq (u : TestVector Vertex) :
    ‖rawDecompositionLinear u‖^2 = ∑ h ∈ componentSupport u, ‖componentRaw h u‖^2 := by
  have he := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (rawDecompositionLinear u)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,rawDecomposition_apply,UniformSpace.Completion.norm_coe] at he
  rw [he]
  apply tsum_eq_sum
  intro h hh
  simp [componentRaw_zero u hh]

 theorem segment_component_subtype (S : Finset Vertex) (hS : IsSegment S) (h : ℕ) :
    IsSegment (S.subtype (fun v => v.height = h)) := by
  constructor
  · intro a ha b hb
    exact hS.1 a (Finset.mem_subtype.mp ha) b (Finset.mem_subtype.mp hb)
  · intro a ha b hb c hac hcb
    exact Finset.mem_subtype.mpr (hS.2 a (Finset.mem_subtype.mp ha) b (Finset.mem_subtype.mp hb) c hac hcb)

 theorem segment_component_image (h : ℕ) (S : Finset (Component h)) (hS : IsSegment S) :
    IsSegment (S.image Subtype.val) := by
  constructor
  · intro a ha b hb
    obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
    exact hS.1 a' ha' b' hb'
  · intro a ha b hb c hac hcb
    obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
    have hc : c.height = h := hac.1.symm.trans a'.property
    exact Finset.mem_image.mpr ⟨⟨c,hc⟩,hS.2 a' ha' b' hb' ⟨c,hc⟩ hac hcb,rfl⟩

 theorem segSum_component_image (h : ℕ) (u : TestVector Vertex) (S : Finset (Component h)) :
    segSum u (S.image Subtype.val) = segSum (componentRaw h u) S := by
  exact Finset.sum_image (fun a ha b hb hab => Subtype.val_injective hab)

 theorem segment_single_height {S : Finset Vertex} (hS : IsSegment S) {v : Vertex} (hv : v ∈ S) :
    ∀ w ∈ S, w.height = v.height := by
  intro w hw
  exact (hS.1 w hw v hv).elim (fun h => h.1) (fun h => h.1.symm)

 theorem segSum_component_subtype (u : TestVector Vertex) (S : Finset Vertex)
    (k : ℕ) (hS : ∀ v ∈ S, v.height = k) (h : ℕ) :
    segSum (componentRaw h u) (S.subtype (fun v => v.height = h)) =
      if h = k then segSum u S else 0 := by
  unfold segSum
  simp only [componentRaw_apply,Finset.sum_subtype_eq_sum_filter]
  by_cases hh : h = k
  · subst h
    rw [ite_eq_left rfl,Finset.filter_eq_self.mpr hS]
  · rw [ite_eq_right hh]
    have hf : S.filter (fun v => v.height = h) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro v hv he
      exact hh (he.symm.trans (hS v hv))
    rw [hf,Finset.sum_empty]

 theorem segSum_sq_components (u : TestVector Vertex) (S : Finset Vertex) (hS : IsSegment S) :
    segSum u S ^ 2 = ∑ h ∈ componentSupport u,
      segSum (componentRaw h u) (S.subtype (fun v => v.height = h))^2 := by
  by_cases hne : S.Nonempty
  · obtain ⟨v,hv⟩ := hne
    simp_rw [segSum_component_subtype u S v.height (segment_single_height hS hv)]
    by_cases hh : v.height ∈ componentSupport u
    · simp [hh]
    · have hz : segSum u S = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        apply Finsupp.notMem_support_iff.mp
        intro hw'
        exact hh (Finset.mem_image.mpr ⟨w,hw',segment_single_height hS hv w hw⟩)
      simp [hz]
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [he,segSum]

 theorem norm_le_rawDecomposition (u : TestVector Vertex) : ‖u‖ ≤ ‖rawDecompositionLinear u‖ := by
  classical
  apply (TestVector.norm_le_iff_testBound u (norm_nonneg _)).mpr
  intro I inst S hS hd
  rw [rawDecomposition_norm_sq]
  simp_rw [segSum_sq_components u _ (hS _)]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro h hh
  change (∑ i, segSum (componentRaw h u) ((S i).subtype (fun v => v.height = h)) ^ 2) ≤
    rho (componentRaw h u) ^ 2
  apply testBound_rho_sq (finsupp_has_testBound (componentRaw h u).toFinsupp)
  · intro i
    exact segment_component_subtype _ (hS i) h
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    exact Finset.disjoint_left.mp (hd hij) (Finset.mem_subtype.mp hvi) (Finset.mem_subtype.mp hvj)

 theorem exists_half_test {W : Type} [PartialOrder W] (u : TestVector W) :
    ∃ (I : Type) (_ : Fintype I) (S : I → Finset W), (∀ i, IsSegment (S i)) ∧
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧ ‖u‖^2 ≤ 2*∑ i, segSum u (S i)^2 := by
  by_cases hz : ‖u‖ = 0
  · exact ⟨PEmpty,inferInstance,PEmpty.elim,by simp,by simp [Pairwise],by simp [hz]⟩
  · have hp : 0 < ‖u‖^2 := sq_pos_of_ne_zero hz
    have hs : ‖u‖^2/2 < squareSup u := by
      rw [← rho_sq (finsupp_has_testBound u.toFinsupp)]
      exact half_lt_self hp
    obtain ⟨r,hr,hl⟩ := (lt_csSup_iff (testBound_l1size u.toFinsupp).bddAbove ⟨0,zero_mem_testValues u⟩).mp hs
    obtain ⟨I,inst,S,hS,hd,rfl⟩ := hr
    exact ⟨I,inst,S,hS,hd,by linarith⟩

 theorem rawDecomposition_norm_le (u : TestVector Vertex) : ‖rawDecompositionLinear u‖ ≤ 2*‖u‖ := by
  let K := componentSupport u
  choose I inst S hS hd hb using (fun h : K => exists_half_test (componentRaw h u))
  let : ∀ h : K, Fintype (I h) := inst
  let A : (Σ h : K, I h) → Finset Vertex := fun i => (S i.1 i.2).image Subtype.val
  have hA : ∀ i, IsSegment (A i) := fun i => segment_component_image i.1 _ (hS i.1 i.2)
  have hdis : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    by_cases hh : i.1 = j.1
    · rcases i with ⟨h,i⟩
      rcases j with ⟨h',j⟩
      dsimp at hh
      subst h'
      apply (Finset.disjoint_image Subtype.val_injective).mpr
      exact hd h (fun he => hij (by cases he; rfl))
    · apply Finset.disjoint_left.mpr
      intro v hvi hvj
      obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp hvi
      obtain ⟨b,hb,heb⟩ := Finset.mem_image.mp hvj
      exact hh (Subtype.ext (a.property.symm.trans ((congrArg Vertex.height (hea.trans heb.symm)).trans b.property)))
  have ht := (testBound_rho_sq (finsupp_has_testBound u.toFinsupp)) (Σ h : K, I h) inferInstance A hA hdis
  have he : (∑ i : (Σ h : K, I h), segSum u (A i)^2) =
      ∑ h : K, ∑ i : I h, segSum (componentRaw h u) (S h i)^2 := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro i hi
    rw [show A ⟨h,i⟩ = (S h i).image Subtype.val from rfl,segSum_component_image]
  rw [he] at ht
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun h hh => hb h)
  rw [← Finset.mul_sum] at hh
  have hsq : ‖rawDecompositionLinear u‖^2 ≤ 2*‖u‖^2 := by
    rw [rawDecomposition_norm_sq,← Finset.sum_coe_sort]
    change (∑ h : K, ‖componentRaw h u‖^2) ≤ 2*‖u‖^2
    exact hh.trans (mul_le_mul_of_nonneg_left ht (by norm_num))
  nlinarith [norm_nonneg u,norm_nonneg (rawDecompositionLinear u)]

noncomputable def rawDecomposition : TestVector Vertex →L[ℝ] lp (fun h => J (Component h)) 2 :=
  rawDecompositionLinear.mkContinuous 2 rawDecomposition_norm_le

 theorem rawDecomposition_dense : DenseRange rawDecomposition := by
  let : DecidableEq ℕ := Classical.decEq ℕ
  apply denseRange_lp_of_singles (fun h => J (Component h)) rawDecompositionLinear
  intro h x
  refine UniformSpace.Completion.induction_on (p := fun a => lp.single 2 h a ∈ rawDecompositionLinear.range.topologicalClosure) x ?_ ?_
  · exact (Submodule.isClosed_topologicalClosure rawDecompositionLinear.range).preimage
      (lp.isometry_single (E := fun h => J (Component h)) (p := 2) h).continuous
  · intro u
    apply Submodule.le_topologicalClosure
    refine ⟨liftComponent h u,?_⟩
    ext j
    by_cases hj : j = h
    · subst j
      simp
    · simp [componentRaw_lift_other h j hj,Pi.single_eq_of_ne hj]

/-- The specified disjoint-component segment completion is canonically
reflexive. Only bounded isomorphisms are needed here; its norm is unchanged. -/
 theorem reflexive_forest_J : Reflexive (J Vertex) := by
  obtain ⟨e⟩ := completion_equiv_of_bounds rawDecomposition 1
    (fun u => by
      change ‖u‖ ≤ 1*‖rawDecompositionLinear u‖
      rw [one_mul]
      exact norm_le_rawDecomposition u)
    rawDecomposition_dense
  exact reflexive_of_equiv e (reflexive_l2 (fun h => J (Component h)) reflexive_component)

end ComponentDecomposition

end

end ForestSpace

end OAI


