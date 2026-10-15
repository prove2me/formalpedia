-- Prove2me | Definitions.Def_OAI_Analysis_ForestSpace_Completion
-- name    : OAI_Analysis_ForestSpace_Completion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:53:12.570027+00:00
-- url     : https://prove2.me/theorems/70489194-3665-40dd-abb7-e2c8325cf44c
-- title:
--   Unit vectors, coordinate functionals and contractive head and tail cuts for the segment norm on finitely supported vectors
-- statement:
--   Let $(V,\le)$ be a partially ordered set. Let $T(V)$ be the real vector space of finitely supported functions $u:V\to\mathbb{R}$ with the disjoint-segment norm $\|u\|=\rho(u)$, where
--
--   $$
--   \rho(u)^2=\sup\Bigl\{\sum_{i=1}^m\Bigl(\sum_{v\in S_i}u(v)\Bigr)^2:\ S_1,\dots,S_m\ \text{pairwise disjoint segments}\Bigr\}
--   $$
--
--   and segments are finite order-convex chains. The completion of $T(V)$ is the Banach space $J(V)$. We say $u$ satisfies the test bound with constant $C$ if every sum in this supremum is at most $C$. A set $H\subseteq V$ is *ancestral* if it is a lower set. For $H\subseteq V$, $\mathbf 1_H u$ keeps the coordinates of $u$ in $H$ and sets the others to $0$. The file provides the following.
--
--   1. **Norm and test bounds.** $\|u\|=\rho(u)$. For every $C\ge0$, $\|u\|\le C$ holds if and only if $u$ satisfies the test bound with constant $C^2$.
--   2. **Unit vectors.** For $v\in V$ and $a\in\mathbb{R}$, $a\delta_v\in T(V)$ is the vector with value $a$ at $v$ and $0$ elsewhere. Its norm is $\|a\delta_v\|=|a|$.
--   3. **Coordinate functionals.** For $v\in V$, the map $\varepsilon_v(u)=u(v)$ is a continuous linear functional on $T(V)$ with $\|\varepsilon_v\|\le1$.
--   4. **Cuts.** For an arbitrary set $H\subseteq V$, the cut is the linear map $u\mapsto\mathbf 1_H u$ on $T(V)$. It satisfies $\mathbf 1_H u+\mathbf 1_{V\setminus H}u=u$, and $\mathbf 1_Hu=u$ whenever $u$ is supported on $H$. For finite $H$, $\mathbf 1_Hu=\sum_{v\in H}u(v)\,\delta_v$.
--   5. **Head and tail operators.** For an ancestral set $H$,
--   $$
--   \|\mathbf 1_H u\|\le\|u\|\qquad\text{and}\qquad\|\mathbf 1_{V\setminus H}u\|\le\|u\|\qquad(u\in T(V)).
--   $$
--   So the head $u\mapsto\mathbf 1_Hu$ and the tail $u\mapsto\mathbf 1_{V\setminus H}u$ are continuous linear operators on $T(V)$ of norm at most $1$.
--
--   These are the finite-dimensional building blocks for the analysis on $J(V)$. The unit vectors and coordinate functionals become the biorthogonal system $(e_v,e_v^*)$. The contractive head and tail operators extend by continuity to $J(V)$, and by composition to its dual, where they give the head–tail decomposition used in the paired estimate.
--
--   **Formalization Note** $T(V)$ is the type synonym `TestVector V` for `V →₀ ℝ`, and `norm_eq_rho` identifies its norm with `rho`. The unit vector is `single v a`, the coordinate functional is `eval v` (built with `mkContinuous`), and the cut is `cut H` (via `Finsupp.filter`). The operators `head H hH` and `tail H hH` take the proof `hH : IsLowerSet H` as an argument. The lemmas `ext`, `zero_apply`, `add_apply`, `smul_apply`, `coe_add`, `coe_smul`, `single_apply`, `cut_apply`, `sum_apply`, `head_apply` and `tail_apply` are evaluation plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Completion.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Completion.lean by skeleton subtraction
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

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

namespace TestVector
variable {V : Type}
@[ext] theorem ext {u v : TestVector V} (h : ∀ a, u a = v a) : u = v := Finsupp.ext h
@[simp] theorem zero_apply (v : V) : (0 : TestVector V) v = 0 := rfl
@[simp] theorem add_apply (u v : TestVector V) (a : V) : (u + v) a = u a + v a := rfl
@[simp] theorem smul_apply (r : ℝ) (u : TestVector V) (a : V) : (r • u) a = r * u a := rfl
@[simp] theorem coe_add (u v : TestVector V) : ⇑(u + v) = u + v := rfl
@[simp] theorem coe_smul (r : ℝ) (u : TestVector V) : ⇑(r • u) = r • ⇑u := rfl

variable [PartialOrder V]
theorem norm_eq_rho (u : TestVector V) : ‖u‖ = rho u := rfl

 theorem norm_le_iff_testBound (u : TestVector V) {C : ℝ} (hC : 0 ≤ C) :
    ‖u‖ ≤ C ↔ TestBound u (C ^ 2) :=
  ⟨testBound_of_rho_le (finsupp_has_testBound u.toFinsupp), rho_le_of_testBound hC⟩

noncomputable def single (v : V) (a : ℝ) : TestVector V := Finsupp.single v a

omit [PartialOrder V] in
@[simp] theorem single_apply [PartialOrder V] (v : V) (a : ℝ) (w : V) :
    single v a w = if v = w then a else 0 := Finsupp.single_apply

 theorem norm_single (v : V) (a : ℝ) : ‖single v a‖ = |a| := by
  change rho (Finsupp.single v a) = |a|
  have hl : l1size (Finsupp.single v a) = |a| := by
    change (Finsupp.single v a).sum (fun _ x => |x|) = |a|
    simp
  apply le_antisymm
  · simpa only [hl] using rho_le_l1size (Finsupp.single v a)
  · simpa using coordinate_le_rho (finsupp_has_testBound (Finsupp.single v a)) v

/-- Coordinate evaluation is bounded by singleton segment tests. -/
noncomputable def eval (v : V) : TestVector V →L[ℝ] ℝ :=
  (show TestVector V →ₗ[ℝ] ℝ from
    { toFun := fun u => u v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).mkContinuous 1 (by
        intro u
        change |u v| ≤ 1 * rho u
        simpa only [one_mul]
          using coordinate_le_rho (finsupp_has_testBound u.toFinsupp) v)

@[simp] theorem eval_apply (v : V) (u : TestVector V) : eval v u = u v := rfl

 theorem eval_norm_le (v : V) : ‖eval v‖ ≤ 1 :=
  (eval v).opNorm_le_bound zero_le_one (fun u => by
    simpa only [eval_apply, Real.norm_eq_abs, one_mul, norm_eq_rho]
      using coordinate_le_rho (finsupp_has_testBound u.toFinsupp) v)

/-- Coordinate restriction, before the boundedness hypothesis is imposed. -/
noncomputable def cut (H : Set V) : TestVector V →ₗ[ℝ] TestVector V where
  toFun u := Finsupp.filter (· ∈ H) u.toFinsupp
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

omit [PartialOrder V] in
@[simp] theorem cut_apply [PartialOrder V] (H : Set V) (u : TestVector V) (v : V) :
    cut H u v = if v ∈ H then u v else 0 := Finsupp.filter_apply _ _ _

 theorem cut_add_compl (H : Set V) (u : TestVector V) : cut H u + cut Hᶜ u = u := by
  ext v
  by_cases hv : v ∈ H <;> simp [hv]

 theorem cut_eq_self {H : Set V} {u : TestVector V} (hu : SupportedOn u H) : cut H u = u := by
  ext v
  by_cases hv : v ∈ H
  · simp [hv]
  · simp [hv, hu v hv]

 theorem norm_cut_le (H : Set V) (hH : IsLowerSet H) (u : TestVector V) :
    ‖cut H u‖ ≤ ‖u‖ := by
  apply (norm_le_iff_testBound _ (norm_nonneg u)).mpr
  have hh := (testBound_rho_sq (finsupp_has_testBound u.toFinsupp)).restrict H hH
  have he : H.indicator ⇑u = ⇑(cut H u) := by
    funext v
    by_cases hv : v ∈ H <;> simp [cut_apply, hv]
  rw [he] at hh
  exact hh

 theorem norm_cut_compl_le (H : Set V) (hH : IsLowerSet H) (u : TestVector V) :
    ‖cut Hᶜ u‖ ≤ ‖u‖ := by
  apply (norm_le_iff_testBound _ (norm_nonneg u)).mpr
  have hh := (testBound_rho_sq (finsupp_has_testBound u.toFinsupp)).restrict_compl H hH
  have he : Hᶜ.indicator ⇑u = ⇑(cut Hᶜ u) := by
    funext v
    by_cases hv : v ∈ H <;> simp [cut_apply, hv]
  rw [he] at hh
  exact hh

omit [PartialOrder V] in
@[simp] theorem sum_apply [PartialOrder V] {ι : Type} (S : Finset ι) (u : ι → TestVector V) (v : V) :
    (∑ i ∈ S, u i) v = ∑ i ∈ S, u i v := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih => simp [ha, ih]

 theorem cut_finite_eq_sum (H : Finset V) (u : TestVector V) :
    cut (H : Set V) u = ∑ v ∈ H, u v • single v 1 := by
  ext w
  simp only [cut_apply, Finset.mem_coe, sum_apply, smul_apply, single_apply,
    mul_ite, mul_one, mul_zero]
  simp

noncomputable def head (H : Set V) (hH : IsLowerSet H) : TestVector V →L[ℝ] TestVector V :=
  (cut H).mkContinuous 1 (by intro u; simpa only [one_mul] using norm_cut_le H hH u)

noncomputable def tail (H : Set V) (hH : IsLowerSet H) : TestVector V →L[ℝ] TestVector V :=
  (cut Hᶜ).mkContinuous 1 (by intro u; simpa only [one_mul] using norm_cut_compl_le H hH u)

@[simp] theorem head_apply (H : Set V) (hH : IsLowerSet H) (u : TestVector V) :
    head H hH u = cut H u := rfl
@[simp] theorem tail_apply (H : Set V) (hH : IsLowerSet H) (u : TestVector V) :
    tail H hH u = cut Hᶜ u := rfl

end TestVector

end

end ForestSpace

end OAI


