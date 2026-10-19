-- Prove2me | Definitions.Def_OAI_Analysis_DiamondDistortion_ModelMaps
-- name    : OAI_Analysis_DiamondDistortion_ModelMaps
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:19:02.099198+00:00
-- url     : https://prove2.me/theorems/3e7845b8-a4ae-4d20-a294-280784a8fa7c
-- title:
--   Hilbertian block structure and separable dual of the linear path-cost forest space
-- statement:
--   This file shows that the linear path-cost norm on the forest of countably branching trees has orthogonal, locally Euclidean components, and concludes that the dual of its completion is separable.
--
--   **Setting.** For $h\ge0$ let $T_h$ be the rooted tree of height $h$ whose vertices are the words over $\mathbb{N}$ of length at most $h$ (the root is the empty word), and let $\mathcal F$ be the forest whose component $h\ge0$ is a copy of $T_{h+1}$. For a finitely supported $v:\mathcal F\to\mathbb{R}$ let $v_h$ be its restriction to component $h$. Given seminorms $s_h$ on the finitely supported functions on $T_{h+1}$, the outer seminorm is $\|v\|_s=\bigl(\sum_{h\ge0}s_h(v_h)^2\bigr)^{1/2}$. Let $J_h:\ell^1(T_h)\to\ell^2(T_h)$, $J_h\mu=\sum_s\mu_s\mathbf 1_{\mathrm{Anc}(s)}$, be the path operator, where $\mathrm{Anc}(s)$ is the set of prefixes of $s$; let $c_{1,h}(v)=\inf\{\|a\|_2+\|\mu\|_1:\ a\in\ell^2(T_h),\ \mu\in\ell^1(T_h),\ a+J_h\mu=v\}$ be the linear path cost on $\ell^2(T_h)$; and let $\|v\|_{\mathrm{lin}}=\bigl(\sum_{h\ge0}c_{1,h+1}(v_h)^2\bigr)^{1/2}$ be the linear forest norm, with completion $X_{\mathrm{lin}}$. Write $\sum_iv_i^2$ for the squared Euclidean norm of $v$.
--
--   1. **Countability.** Every vertex set $T_h$ is countable.
--   2. **Outer sums.** For any seminorms $s_h$: if $C\subseteq\mathbb{N}$ is a finite set containing every component met by the support of $v$, then $\|v\|_s^2=\sum_{h\in C}s_h(v_h)^2$; restricting $v$ to the components in an arbitrary set $C\subseteq\mathbb{N}$ does not increase $\|v\|_s$; and if $v$ and $w$ are supported on disjoint sets of components, then $\|v+w\|_s^2\le\|v\|_s^2+\|w\|_s^2$.
--   3. **Path cost versus the Euclidean norm.** $\|J_h\mu\|_2\le(h+1)\|\mu\|_1$ for $\mu\in\ell^1(T_h)$, and $\|v\|_2\le(h+1)\,c_{1,h}(v)$ for $v\in\ell^2(T_h)$.
--   4. **Euclidean comparison on finitely many components.** For every finitely supported $v$ on $\mathcal F$ one has $\|v\|_{\mathrm{lin}}^2\le\sum_iv_i^2$; and if $C\subseteq\mathbb{N}$ is finite and every vertex in the support of $v$ lies in a component $h\in C$, then
--   $$\sum_iv_i^2\le(\max C+2)^2\,\|v\|_{\mathrm{lin}}^2.$$
--   5. **Hilbertian blocks.** The linear forest norm has Hilbertian blocks along the component map $(h,s)\mapsto h$: vectors supported on disjoint sets of components satisfy $\|v+w\|_{\mathrm{lin}}^2\le\|v\|_{\mathrm{lin}}^2+\|w\|_{\mathrm{lin}}^2$; restriction to any set of components does not increase the norm; and for every finite set $C$ of components, all $v$ supported in $C$ satisfy the upper estimate $\|v\|_{\mathrm{lin}}^2\le B\sum_iv_i^2$ with $B=1$ and the lower estimate $\sum_iv_i^2\le L\|v\|_{\mathrm{lin}}^2$ with $L=(\max C+2)^2$.
--   6. **Separable dual.** The dual $X_{\mathrm{lin}}^*$, the space of all continuous linear functionals on $X_{\mathrm{lin}}$ with the operator norm, is separable.
--
--   The last item is obtained from the general density criterion for duals of coordinate completions: when the blocks are orthogonal, restrictions to blocks are contractive and the norm is equivalent to the Euclidean norm on finitely many blocks, finite combinations of coordinate functionals are dense in the dual, which is therefore separable because the index set is countable.
--
--   **Formalization Note** The declarations are `RecursiveModel.countableCoord`; `outer_sq`, `outer_contractive` and `outer_orthogonal` for `outerSeminorm`, with `aggregate_sq`, `components_zero`, `components_filter`, `outer_support` and `energy_components` as bookkeeping; `PathModel.path_norm`, `linear_l2`, `finite_l2_sq`, `linear_upper` and `linear_lower` (whose constant is `(((C.sup id : ℕ) : ℝ) + 2)^2`, so $\max\emptyset=0$); `linearBlocks : linearData.HilbertBlocks Sigma.fst`; and the instance `linearDualSeparable` for `StrongDual ℝ LinearSpace`. A section `StartModel.ContractiveMap` only declares variables, and `ite_eq_left`, `ite_eq_right` are local aliases.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/ModelMaps.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/ModelMaps.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiamondDistortion mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_DiamondGraph
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateSpace
import Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_InfimalCost
import Definitions.Def_OAI_Analysis_DiamondDistortion_PathModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_StartModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateDual
import Definitions.Def_OAI_Analysis_DiamondDistortion_Incomparable

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace RecursiveModel
instance countableCoord (h : ℕ) : Countable (Coord h) := by
  induction h with
  | zero => exact inferInstanceAs (Countable Unit)
  | succ h ih => exact inferInstanceAs (Countable (Unit ⊕ (ℕ × Coord h)))

lemma aggregate_sq {ι : Type*} (f : ι →₀ ℝ) :
    (aggregate 2 f)^2=∑ i ∈ f.support,f i^2 := by
  have hh := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (finiteLp 2 f)
  have he : (aggregate 2 f)^2=∑' i,f i^2 := by
    simpa only [aggregate,ENNReal.toReal_ofNat,Real.rpow_two,finiteLp_apply,Real.norm_eq_abs,sq_abs] using hh
  rw [he]
  exact tsum_eq_sum (fun i hi => by rw [Finsupp.notMem_support_iff.mp hi]; norm_num)

lemma components_zero (p : ForestVec) (h : ℕ) (hh : h ∉ p.support.image Sigma.fst) :
    components p h=0 := by
  ext i
  change p ⟨h,i⟩=0
  apply Finsupp.notMem_support_iff.mp
  intro hi
  exact hh (Finset.mem_image.mpr ⟨⟨h,i⟩,hi,rfl⟩)

lemma outer_support (s : ∀ h,Seminorm ℝ (Vec (h+1))) (p : ForestVec) :
    (outerValues s p).support ⊆ p.support.image Sigma.fst := by
  intro h hh
  by_contra hn
  have he : outerValues s p h=0 := by rw [outerValues_apply,components_zero p h hn,map_zero]
  exact (Finsupp.mem_support_iff.mp hh) he

lemma outer_sq (s : ∀ h,Seminorm ℝ (Vec (h+1))) (p : ForestVec) (C : Finset ℕ)
    (hC : p.support.image Sigma.fst ⊆ C) :
    (outerSeminorm s p)^2=∑ h ∈ C,(s h (components p h))^2 := by
  change (aggregate 2 (outerValues s p))^2=_
  rw [aggregate_sq]
  apply Finset.sum_subset ((outer_support s p).trans hC)
  intro h _ hh
  rw [Finsupp.notMem_support_iff.mp hh]
  norm_num

lemma components_filter (p : ForestVec) (C : Set ℕ) (h : ℕ) :
    components (p.filter (fun i => i.1 ∈ C)) h=if h ∈ C then components p h else 0 := by
  ext i
  by_cases hh : h ∈ C
  · rw [ite_eq_left hh]
    change (p.filter (fun i => i.1 ∈ C)) ⟨h,i⟩=p ⟨h,i⟩
    rw [Finsupp.filter_apply,ite_eq_left hh]
  · rw [ite_eq_right hh]
    change (p.filter (fun i => i.1 ∈ C)) ⟨h,i⟩=0
    rw [Finsupp.filter_apply,ite_eq_right hh]

lemma outer_contractive (s : ∀ h,Seminorm ℝ (Vec (h+1))) (p : ForestVec) (C : Set ℕ) :
    outerSeminorm s (p.filter (fun i => i.1 ∈ C)) ≤ outerSeminorm s p := by
  apply aggregate_mono 2
  · exact outerValues_nonneg s _
  · intro h
    rw [outerValues_apply,outerValues_apply,components_filter]
    split_ifs
    · exact le_rfl
    · rw [map_zero]; exact apply_nonneg _ _

lemma outer_orthogonal (s : ∀ h,Seminorm ℝ (Vec (h+1))) (p q : ForestVec)
    (hd : Disjoint (p.support.image Sigma.fst) (q.support.image Sigma.fst)) :
    (outerSeminorm s (p+q))^2 ≤ (outerSeminorm s p)^2+(outerSeminorm s q)^2 := by
  let C := p.support.image Sigma.fst ∪ q.support.image Sigma.fst
  have hp : p.support.image Sigma.fst ⊆ C := Finset.subset_union_left
  have hq : q.support.image Sigma.fst ⊆ C := Finset.subset_union_right
  have hpq : (p+q).support.image Sigma.fst ⊆ C := by
    intro h hh
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hh
    rcases Finset.mem_union.mp (Finsupp.support_add hi) with hi | hi
    · exact hp (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    · exact hq (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
  rw [outer_sq s p C hp,outer_sq s q C hq,outer_sq s (p+q) C hpq,← Finset.sum_add_distrib]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro h _
  rw [map_add,DFinsupp.add_apply]
  by_cases hh : h ∈ p.support.image Sigma.fst
  · have hhq := Finset.disjoint_left.mp hd hh
    rw [components_zero q h hhq,add_zero,map_zero,zero_pow (by decide : 2 ≠ 0),add_zero]
  · rw [components_zero p h hh,zero_add,map_zero,zero_pow (by decide : 2 ≠ 0),zero_add]

lemma energy_components (p : ForestVec) (C : Finset ℕ) (hC : p.support.image Sigma.fst ⊆ C) :
    (∑ i ∈ p.support,p i^2)=∑ h ∈ C,∑ i ∈ (components p h).support,(components p h i)^2 := by
  have he (h : ℕ) : p.split h=components p h := by ext i; rw [Finsupp.split_apply]; rfl
  have hh := p.sigma_sum (fun _ a => a^2)
  simp only [Finsupp.sum,he] at hh
  rw [hh]
  have hes : p.splitSupport=p.support.image Sigma.fst := by
    ext h
    simp only [Finsupp.splitSupport,Finset.mem_image]
  rw [hes]
  apply Finset.sum_subset hC
  intro h _ hh
  have hzero := components_zero p h hh
  rw [hzero,Finsupp.support_zero,Finset.sum_empty]

end RecursiveModel

namespace PathModel
open RecursiveModel
lemma path_norm (h : ℕ) (μ : L1 h) : ‖path h μ‖ ≤ (h+1:ℝ)*‖μ‖ := by
  have hb : ‖path h‖ ≤ (h+1:ℝ) :=
    LinearMap.mkContinuous_norm_le _ (by positivity : (0:ℝ) ≤ h+1) _
  exact ((path h).le_opNorm μ).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

lemma linear_l2 (h : ℕ) (v : L2 h) : ‖v‖ ≤ (h+1:ℝ)*cost 1 h v := by
  apply (presentation 1 h).bound v (by positivity : (0:ℝ) ≤ h+1)
  intro d hd
  change d.fst+path h d.snd=v at hd
  rw [← hd,WithLp.prod_norm_eq_of_L1]
  have hb := (norm_add_le d.fst (path h d.snd)).trans (add_le_add le_rfl (path_norm h d.snd))
  have hhn : 1 ≤ (h+1:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) h]
  have hn := norm_nonneg d.fst
  nlinarith

lemma finite_l2_sq (h : ℕ) (v : Vec h) :
    ‖finiteEmbedding h v‖^2=∑ i ∈ v.support,v i^2 := aggregate_sq v

lemma linear_upper (p : ForestVec) :
    (linearForestSeminorm p)^2 ≤ ∑ i ∈ p.support,p i^2 := by
  let C := p.support.image Sigma.fst
  rw [energy_components p C (by rfl)]
  change (outerSeminorm (fun h => finiteCost 1 (h+1)) p)^2 ≤ _
  rw [outer_sq _ p C (by rfl)]
  apply Finset.sum_le_sum
  intro h _
  rw [← finite_l2_sq]
  exact (sq_le_sq₀ (apply_nonneg _ _) (norm_nonneg _)).mpr (linear_le_norm (h+1) _)

lemma linear_lower (C : Finset ℕ) (p : ForestVec)
    (hp : ∀ i ∈ p.support,i.1 ∈ C) :
    (∑ i ∈ p.support,p i^2) ≤ (((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+2)^2*(linearForestSeminorm p)^2 := by
  have hC : p.support.image Sigma.fst ⊆ C := by
    rintro _ hh
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hh
    exact hp i hi
  rw [energy_components p C hC]
  change _ ≤ _*(outerSeminorm (fun h => finiteCost 1 (h+1)) p)^2
  rw [outer_sq _ p C hC,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  rw [← finite_l2_sq]
  have hb := linear_l2 (h+1) (finiteEmbedding _ (components p h))
  have hm : ((h+1:ℕ):ℝ)+1 ≤ ((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+2 := by
    have he : (h:ℝ) ≤ ((C.sup (id : ℕ → ℕ) : ℕ) : ℝ) := by exact_mod_cast Finset.le_sup (f := id) hh
    push_cast
    linarith
  have hpos : 0 ≤ cost 1 (h+1) (finiteEmbedding _ (components p h)) := apply_nonneg _ _
  have hb' := hb.trans (mul_le_mul_of_nonneg_right hm hpos)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb'
  simpa only [mul_pow,finiteCost,Seminorm.comp_apply] using hs

lemma linearBlocks : linearData.HilbertBlocks Sigma.fst where
  orthogonal p q hd := outer_orthogonal _ p q (by
    simpa only [Finset.disjoint_left,Finset.mem_image] using hd)
  contractive := outer_contractive _
  upper C := ⟨1,by norm_num,fun p _ => by simpa only [linearData,one_mul] using linear_upper p⟩
  lower C := ⟨(((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+2)^2,by positivity,
    fun p hp => linear_lower C p hp⟩
instance linearDualSeparable : TopologicalSpace.SeparableSpace (StrongDual ℝ LinearSpace) :=
  linearData.dual_separable Sigma.fst linearBlocks
end PathModel

namespace StartModel
open RecursiveModel PathModel
namespace ContractiveMap
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
end ContractiveMap

end StartModel

end DiamondDistortion

end

end OAI


